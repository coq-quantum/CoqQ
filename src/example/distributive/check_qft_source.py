#!/usr/bin/env python3
"""Audit the actual qft.isq transcription against the checked Rocq model.

Run from any directory:
    python3 src/example/distributive/check_qft_source.py

Build the proof libraries first with ``opam exec --switch=coqq -- dune build``.
Only Python's standard library is used. Generated Rocq files live in a temporary
directory, and coqq/coqc checks every rank of each accepted eight-qubit layout.

This is an executable source transcription audit, not a certified isQ parser,
compiler, QMPI implementation, or floating-point/gate implementation. Dynamic
ancilla/pair allocation is represented by private preallocated slots and fresh
ideal Bell resources; the model observes logical data, not all auxiliary reset,
allocation, deallocation, or runtime effects. Unsupported syntax fails closed.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[3]
ACCEPTED_NODES = (2, 3, 4, 8)
MAX_WORK = 10_000


class AuditError(Exception):
    """The source or its correspondence could not be checked."""


@dataclass(frozen=True)
class Token:
    text: str
    line: int


TOKEN = re.compile(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|\*\*|==|!=|<=|>=|[{}()\[\];,:.+*/<>=-]")


def tokenize(source: str) -> list[Token]:
    """Lex the supported subset; comments never enter a signature or AST."""
    result: list[Token] = []
    pos, line = 0, 1
    while pos < len(source):
        if source[pos].isspace():
            line += source[pos] == "\n"
            pos += 1
            continue
        if source.startswith("//", pos):
            end = source.find("\n", pos)
            pos = len(source) if end < 0 else end
            continue
        if source.startswith("/*", pos):
            end = source.find("*/", pos + 2)
            if end < 0:
                raise AuditError(f"line {line}: unterminated block comment")
            line += source[pos : end + 2].count("\n")
            pos = end + 2
            continue
        match = TOKEN.match(source, pos)
        if not match:
            raise AuditError(f"line {line}: unsupported token near {source[pos:pos + 20]!r}")
        result.append(Token(match.group(), line))
        pos = match.end()
    return result


def signature(source: str) -> tuple[str, ...]:
    return tuple(token.text for token in tokenize(source))


# Full signatures deliberately include parameters, message order/tags, the R
# expression, both main guards, allocation, initialization, and the qft call.
# They are source contracts, not hashes of an already generated Coq trace.
FIXED_UNITS = {
    "teleport_send": """
        unit teleport_send(qbit q, int to) {
          qbit pair; create_epr(to, 99, pair); CNOT(q, pair); H(q);
          qmpi_csend(M(pair), to, 88); qmpi_csend(M(q), to, 88);
        }
    """,
    "teleport_recv": """
        unit teleport_recv(qbit q, int from) {
          qbit pair; create_epr(from, 99, pair);
          if (qmpi_crecv(from, 88)) { X(pair); }
          if (qmpi_crecv(from, 88)) { Z(pair); }
          SWAP(pair, q);
        }
    """,
    "R": """
        procedure R(int k, qbit q) {
          double phase = pi / 2 ** (k - 1);
          ctrl GPhase(phase, q);
        } deriving gate
    """,
    "main": """
        procedure main() {
          int n = 8; int np = qmpi_size();
          if (np < 2) { print -1; return; }
          int nqubit_normal = (n + np - 1) / np;
          int nqubit_left = n - (np - 1) * nqubit_normal;
          if (nqubit_left < 1) { print -1; return; }
          int rank = qmpi_comm_rank(); int nqubit = nqubit_normal;
          if (rank == 0) { nqubit = nqubit_left; }
          qbit q[nqubit]; X(q[0]); qft(q, n, np, rank, nqubit_normal);
        }
    """,
}
QFT_HEADER = signature("unit qft(qbit q[], int n, int np, int rank, int nqubit_normal)")


class Reader:
    def __init__(self, tokens: list[Token]):
        self.tokens, self.pos = tokens, 0

    def peek(self) -> str:
        return self.tokens[self.pos].text if self.pos < len(self.tokens) else "<end>"

    def pop(self) -> str:
        token = self.peek()
        if token == "<end>":
            self.fail("unexpected end of input")
        self.pos += 1
        return token

    def expect(self, token: str) -> None:
        if self.pop() != token:
            self.fail(f"expected {token!r}")

    def name(self) -> str:
        value = self.pop()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", value):
            self.fail("expected an identifier")
        return value

    def fail(self, message: str) -> None:
        index = min(self.pos, len(self.tokens) - 1)
        line = self.tokens[index].line if self.tokens else 1
        raise AuditError(f"line {line}: {message} (near {self.peek()!r})")


def source_units(tokens: list[Token]) -> dict[str, tuple[list[Token], list[Token]]]:
    reader = Reader(tokens)
    for imported in ("std", "qmpi", "lib"):
        reader.expect("import")
        reader.expect(imported)
        reader.expect(";")
    units = {}
    while reader.peek() != "<end>":
        start = reader.pos
        if reader.pop() not in ("unit", "procedure"):
            reader.fail("unsupported top-level declaration")
        name = reader.name()
        while reader.peek() not in ("{", "<end>"):
            reader.pop()
        header_end = reader.pos
        reader.expect("{")
        body_start, depth = reader.pos, 1
        while depth:
            value = reader.pop()
            depth += (value == "{") - (value == "}")
        body_end = reader.pos - 1
        if reader.peek() == "deriving":
            if name != "R":
                reader.fail("gate derivation is supported only on R")
            reader.expect("deriving")
            reader.expect("gate")
        if name in units:
            raise AuditError(f"duplicate unit {name}")
        units[name] = (tokens[start:reader.pos], tokens[body_start:body_end])
        if name == "qft" and tuple(t.text for t in tokens[start:header_end]) != QFT_HEADER:
            raise AuditError("qft's signature differs from the audited interface")
    if set(units) != {*FIXED_UNITS, "qft"}:
        raise AuditError("source must contain exactly teleport_send, teleport_recv, R, qft, main")
    for name, expected in FIXED_UNITS.items():
        actual = tuple(t.text for t in units[name][0])
        wanted = signature(expected)
        if actual != wanted:
            mismatch = next((i for i, pair in enumerate(zip(actual, wanted)) if pair[0] != pair[1]),
                            min(len(actual), len(wanted)))
            raise AuditError(f"{name}: full token signature changed at token {mismatch + 1}; "
                             "update and review the source/model contract before accepting it")
    return units


# Restricted AST tuples: expressions and statement forms retain actual source
# expressions. No model trace is imported, hardcoded, or used by this parser.
PRECEDENCE = {"==": 1, "!=": 1, "<": 1, ">": 1, "<=": 1, ">=": 1,
              "+": 2, "-": 2, "*": 3, "/": 3, "**": 4}


class Parser(Reader):
    def expression(self, minimum: int = 0):
        value = self.pop()
        if value in ("-", "+"):
            left = ("unary", value, self.expression(4))
        elif value == "(":
            left = self.expression()
            self.expect(")")
        elif value.isdecimal():
            left = ("integer", int(value))
        elif re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", value):
            left = ("name", value)
            if self.peek() == ".":
                self.pop()
                self.expect("length")
                left = ("length", left)
            elif self.peek() == "[":
                self.pop()
                left = ("index", left, self.expression())
                self.expect("]")
        else:
            self.fail("unsupported expression")
        while self.peek() in PRECEDENCE and PRECEDENCE[self.peek()] >= minimum:
            operator = self.pop()
            level = PRECEDENCE[operator]
            right = self.expression(level if operator == "**" else level + 1)
            left = ("binary", operator, left, right)
        return left

    def block(self):
        self.expect("{")
        result = self.statements("}")
        self.expect("}")
        return result

    def statements(self, end: str = "<end>") -> list:
        result = []
        while self.peek() != end:
            if self.peek() == "<end>":
                self.fail("unterminated block")
            result.append(self.statement())
        return result

    def statement(self):
        value = self.pop()
        if value == "int":
            name = self.name()
            self.expect("=")
            expr = self.expression()
            self.expect(";")
            return ("declare", name, expr)
        if value == "qbit":
            name = self.name()
            self.expect(";")
            if name != "anc":
                self.fail("only the remote-loop anc allocation is supported")
            return ("ancilla", name)
        if value == "for":
            name = self.name()
            self.expect("in")
            start = self.expression()
            self.expect(":")
            stop = self.expression()
            step = ("integer", 1)
            if self.peek() == ":":
                self.pop()
                step = self.expression()
            return ("for", name, start, stop, step, self.block())
        if value == "if":
            self.expect("(")
            condition = self.expression()
            self.expect(")")
            yes, no = self.block(), []
            if self.peek() == "else":
                self.pop()
                no = self.block()
            return ("if", condition, yes, no)
        controlled = value == "ctrl"
        name = self.name() if controlled else value
        if self.peek() == "=":
            if controlled:
                self.fail("controlled assignment is unsupported")
            self.pop()
            expr = self.expression()
            self.expect(";")
            return ("assign", name, expr)
        if (name, controlled) not in {("H", False), ("R", True),
                                     ("teleport_send", False), ("teleport_recv", False)}:
            self.fail(f"unsupported qft statement {name!r}")
        self.expect("(")
        args = []
        if self.peek() != ")":
            args.append(self.expression())
            while self.peek() == ",":
                self.pop()
                args.append(self.expression())
        self.expect(")")
        self.expect(";")
        return ("call", name, args)


@dataclass(frozen=True)
class Wire:
    rank: int
    kind: str
    index: int  # q index, or anc's outer-loop origin


class Environment:
    def __init__(self, parent=None):
        self.parent, self.values = parent, {}

    def get(self, name):
        if name in self.values:
            return self.values[name]
        if self.parent:
            return self.parent.get(name)
        raise AuditError(f"unbound source variable {name}")

    def declare(self, name, value):
        if name in self.values:
            raise AuditError(f"duplicate declaration of {name}")
        self.values[name] = value

    def assign(self, name, value):
        if name in self.values:
            integer(self.values[name])
            self.values[name] = integer(value)
        elif self.parent:
            self.parent.assign(name, value)
        else:
            raise AuditError(f"assignment to undeclared variable {name}")


def integer(value) -> int:
    if not isinstance(value, int):
        raise AuditError("integer expression used a non-integer value")
    return value


def evaluate(expr, env: Environment):
    kind, *args = expr
    if kind == "integer":
        return args[0]
    if kind == "name":
        return env.get(args[0])
    if kind == "length":
        array = evaluate(args[0], env)
        if not isinstance(array, tuple):
            raise AuditError(".length is supported only for the local q array")
        return len(array)
    if kind == "index":
        array, index = evaluate(args[0], env), integer(evaluate(args[1], env))
        if not isinstance(array, tuple) or not 0 <= index < len(array):
            raise AuditError(f"out-of-bounds/non-array q access at index {index}")
        return array[index]
    if kind == "unary":
        value = integer(evaluate(args[1], env))
        return -value if args[0] == "-" else value
    operator, left, right = args
    a, b = integer(evaluate(left, env)), integer(evaluate(right, env))
    if operator == "+":
        return a + b
    if operator == "-":
        return a - b
    if operator == "*":
        return a * b
    if operator == "/":
        if b == 0:
            raise AuditError("division by zero")
        return (abs(a) // abs(b)) * (-1 if (a < 0) != (b < 0) else 1)
    if operator == "**":
        if not 0 <= b <= 30:
            raise AuditError("unsupported exponent")
        return a**b
    return {"==": a == b, "!=": a != b, "<": a < b, ">": a > b,
            "<=": a <= b, ">=": a >= b}[operator]


def rank_events(body, nodes: int, rank: int, widths: list[int]) -> list[tuple]:
    env = Environment()
    for name, value in {"n": 8, "np": nodes, "rank": rank,
                        "nqubit_normal": widths[-1],
                        "q": tuple(Wire(rank, "q", i) for i in range(widths[rank]))}.items():
        env.declare(name, value)
    events, allocated = [], set()
    work = 0

    def execute(statements, current):
        nonlocal work
        for statement in statements:
            work += 1
            if work > MAX_WORK:
                raise AuditError("source interpretation exceeded the bounded audit workload")
            kind, *args = statement
            if kind == "declare":
                current.declare(args[0], integer(evaluate(args[1], current)))
            elif kind == "assign":
                current.assign(args[0], evaluate(args[1], current))
            elif kind == "ancilla":
                origin = integer(current.get("ir"))
                if not rank < origin < nodes or origin in allocated:
                    raise AuditError("anc must be declared once per remote outer-loop origin")
                allocated.add(origin)
                current.declare(args[0], Wire(rank, "anc", origin))
            elif kind == "if":
                execute(args[1] if integer(evaluate(args[0], current)) else args[2],
                        Environment(current))
            elif kind == "for":
                name, start, stop, step, loop_body = args
                start, stop, step = (integer(evaluate(e, current)) for e in (start, stop, step))
                if step == 0:
                    raise AuditError("zero loop step")
                loop_range = range(start, stop, step)  # isQ's end-exclusive ranges
                if len(loop_range) > MAX_WORK:
                    raise AuditError("source loop exceeded the bounded audit workload")
                for value in loop_range:
                    child = Environment(current)
                    child.declare(name, value)
                    execute(loop_body, child)
            elif kind == "call":
                name, expressions = args
                values = [evaluate(e, current) for e in expressions]
                arity = {"H": 1, "R": 3, "teleport_send": 2, "teleport_recv": 2}[name]
                if len(values) != arity:
                    raise AuditError(f"wrong arity for {name}")
                if name == "R":
                    power, control, target = values
                    if integer(power) < 1 or not all(isinstance(w, Wire) for w in (control, target)):
                        raise AuditError("invalid controlled-R arguments")
                    events.append(("phase", target, control, power))
                else:
                    if not isinstance(values[0], Wire):
                        raise AuditError(f"{name} expects a qubit")
                    if name == "H":
                        events.append(("hadamard", values[0]))
                    else:
                        peer = integer(values[1])
                        if not 0 <= peer < nodes or peer == rank:
                            raise AuditError("invalid teleport endpoint")
                        events.append(("send" if name.endswith("send") else "receive", values[0], peer))
    execute(body, env)
    return events


def logical_traces(events: list[list[tuple]], widths: list[int]) -> list[list[tuple]]:
    """Resolve physical carriers by actual matching front-of-queue transfers."""
    nodes, offsets = len(widths), [sum(widths[:r]) for r in range(len(widths))]
    initial = {Wire(r, "q", i): offsets[r] + i for r in range(nodes) for i in range(widths[r])}
    carrier = dict(initial)
    owner = {target: wire.rank for wire, target in initial.items()}
    positions, result = [0] * nodes, [[] for _ in range(nodes)]

    def active(wire):
        value = carrier.get(wire)
        if value is None:
            raise AuditError(f"operation uses an empty/unreceived logical carrier {wire}")
        return value

    while any(positions[r] < len(events[r]) for r in range(nodes)):
        progress = False
        for rank in range(nodes):
            if positions[rank] == len(events[rank]):
                continue
            event = events[rank][positions[rank]]
            kind, wire, *args = event
            if kind in ("hadamard", "phase"):
                target = active(wire)
                operation = ("HadamardTarget", target) if kind == "hadamard" else (
                    "ControlledTarget", target, active(args[0]), args[1])
                result[rank].append(operation)
                positions[rank] += 1
                progress = True
            elif kind == "send":
                peer = args[0]
                if positions[peer] == len(events[peer]):
                    continue
                receiver = events[peer][positions[peer]]
                if receiver[0] != "receive" or receiver[2] != rank:
                    continue
                target, destination = active(wire), receiver[1]
                if carrier.get(destination) is not None:
                    raise AuditError(f"transfer overwrites active data at {destination}")
                if (destination.kind == "q" and initial[destination] != target) or (
                    destination.kind == "anc" and destination.index != owner[target]
                ):
                    raise AuditError("receive destination differs from the model's data/origin slot")
                carrier[wire], carrier[destination] = None, target
                result[rank].append(("SendTarget", target, peer))
                result[peer].append(("ReceiveTarget", target, rank))
                positions[rank] += 1
                positions[peer] += 1
                progress = True
        if not progress:
            raise AuditError(f"unmatched/deadlocked source teleport queues at positions {positions}")
    if any(carrier.get(wire) != target for wire, target in initial.items()):
        raise AuditError("source fails to return every logical qubit to its original data slot")
    return result


def rocq_source(traces: dict[int, list[list[tuple]]]) -> str:
    lines = [
        "From mathcomp Require Import all_ssreflect.",
        "From quantum.example.distributive Require Import qft.",
        "Import DistributedQFTSchedule DistributedQFTSource DistributedQFTInstance DistributedQFTProgram.",
        "Set Implicit Arguments.",
        "Unset Strict Implicit.",
        "Unset Printing Implicit Defensive.",
        "",
        "(* Generated from the actual qft.isq token stream, not from rank_source. *)",
    ]
    for nodes, ranks in traces.items():
        lines += [f"Lemma literal_layout_{nodes} : valid_source_layout 8 {nodes}.",
                  "Proof. apply: valid_eight_members. by vm_compute. Qed."]
        for rank, operations in enumerate(ranks):
            actions = [f"RankedAction {rank} ({op[0]} {' '.join(map(str, op[1:]))})"
                       for op in operations]
            literal = "[::\n    " + ";\n    ".join(actions) + "]" if actions else "[::]"
            suffix = f"p{nodes}_r{rank}"
            lines += [f"Definition literal_actions_{suffix} : seq ranked_action := {literal}.",
                      f"Example literal_source_{suffix} :",
                      f"  literal_actions_{suffix} = rank_source (source_layout literal_layout_{nodes}) {rank}.",
                      "Proof. by vm_compute. Qed.",
                      f"Lemma literal_rank_bound_{suffix} : ({rank} < {nodes})%N.",
                      "Proof. by vm_compute. Qed.",
                      f"Definition literal_rank_{suffix} : 'I_{nodes} := Ordinal literal_rank_bound_{suffix}.",
                      f"Example literal_native_script_{suffix} (memory : physical_memory literal_layout_{nodes}) :",
                      f"  qft_rank_script memory literal_rank_{suffix} =",
                      f"    code_actions memory literal_rank_{suffix} literal_actions_{suffix}.",
                      f"Proof. rewrite qft_rank_script_source. by rewrite -literal_source_{suffix}. Qed.", ""]
    lines += ["(* Checked bridges from rank_source to the written native DL program. *)",
              "Check DistributedQFTProgram.qft_rank_script_source.",
              "Check DistributedQFTProgram.qft_rank_scriptE.",
              "Check DistributedQFTProgram.qft_programE.",
              "Check DistributedQFTProgram.qft_main_input_local.", ""]
    return "\n".join(lines)


def check_libraries() -> tuple:
    """Require matching source copies and fresh .vo files for all three files."""
    snapshots = []
    build_first = "rebuild first: opam exec --switch=coqq -- dune build"
    for name in ("qft_model", "qft_teleport", "qft"):
        source = ROOT / f"src/example/distributive/{name}.v"
        copied = ROOT / f"_build/default/src/example/distributive/{name}.v"
        compiled = copied.with_suffix(".vo")
        if not copied.is_file() or not compiled.is_file():
            raise AuditError(f"missing built {name} library; {build_first}")
        original_bytes, copied_bytes = source.read_bytes(), copied.read_bytes()
        if original_bytes != copied_bytes:
            raise AuditError(f"{name}.v differs from its Dune build copy; {build_first}")
        compiled_time = compiled.stat().st_mtime_ns
        if compiled_time < max(source.stat().st_mtime_ns, copied.stat().st_mtime_ns):
            raise AuditError(f"{name}.vo is older than its source or build copy; {build_first}")
        snapshots.append((hashlib.sha256(original_bytes).digest(),
                          hashlib.sha256(compiled.read_bytes()).digest()))
    return tuple(snapshots)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--source", type=Path, default=ROOT / "qft.isq",
                        help="source file to audit (default: repository qft.isq)")
    args = parser.parse_args()
    try:
        source_bytes = args.source.read_bytes()
        units = source_units(tokenize(source_bytes.decode("utf-8")))
        body = Parser(units["qft"][1]).statements()
        traces = {}
        for nodes in ACCEPTED_NODES:
            normal = (8 + nodes - 1) // nodes
            widths = [8 - (nodes - 1) * normal] + [normal] * (nodes - 1)
            events = [rank_events(body, nodes, rank, widths) for rank in range(nodes)]
            traces[nodes] = logical_traces(events, widths)
        library = ROOT / "_build/default/src"
        libraries_before = check_libraries()
        with tempfile.TemporaryDirectory(prefix="coqq-qft-source-") as temporary:
            proof = Path(temporary) / "literal_qft_source.v"
            generated = rocq_source(traces)
            proof.write_text(generated, encoding="utf-8")
            command = ["opam", "exec", "--switch=coqq", "--", "coqc", "-q",
                       "-w", "-notation-overridden,-notation-incompatible-prefix,-deprecated,-ambiguous-paths",
                       "-R", str(library), "quantum", str(proof)]
            checked = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=False)
            if checked.returncode:
                location = re.search(r'File "[^"]+", line ([0-9]+)', checked.stderr)
                context = ""
                if location:
                    prefix = generated.splitlines()[:int(location.group(1))]
                    declarations = [re.match(r"(?:Example|Lemma) ([A-Za-z_0-9]+)", line)
                                    for line in prefix]
                    names = [match.group(1) for match in declarations if match]
                    context = f" ({names[-1]})" if names else ""
                raise AuditError(f"Rocq rejected the literal source/model equalities{context}:\n" +
                                 checked.stdout + checked.stderr)
        if args.source.read_bytes() != source_bytes or check_libraries() != libraries_before:
            raise AuditError("source or proof libraries changed during the audit; rebuild and rerun")
        count = sum(len(rank) for ranks in traces.values() for rank in ranks)
        print("PASS: full teleport_send, teleport_recv, R, and main token signatures.")
        print(f"PASS: {count} literal operations across 17 rank traces (p=2,3,4,8), checked by coqq/Rocq.")
        for nodes, ranks in traces.items():
            operations = [op for rank in ranks for op in rank]
            counts = {name: sum(op[0] == name for op in operations)
                      for name in ("HadamardTarget", "ControlledTarget", "SendTarget")}
            print(f"  p={nodes}: {counts['HadamardTarget']} H, "
                  f"{counts['ControlledTarget']} controlled phases, {counts['SendTarget']} teleport hops.")
        print("PASS: existing rank-source, native-script, and DL.Program bridges are available.")
        print("PASS: all 17 literal traces equal the corresponding native rank scripts for every physical_memory.")
        print("PASS: the source-main local-bit initialization bridge is available.")
        print(f"Source SHA256: {hashlib.sha256(source_bytes).hexdigest()}")
        print("Scope: executable transcription audit; ideal Bell service, exact gates, data observation.")
        print("This does not certify an isQ parser/compiler, QMPI, floating point, or auxiliary allocation/reset traces.")
        return 0
    except (AuditError, OSError, UnicodeError, OverflowError, RecursionError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
