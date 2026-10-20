# Validation

## Current corrected-source correspondence checkpoint

Date: 2026-10-07. The complete corrected [qft.isq](../../../qft.isq) marks
the rank-zero phase-index fix as `FIX F1`, the nonpositive-allocation guard
as `FIX F2`, and the returned-output comment as `CLARIFICATION C1`.
The [source corrections](QFT_PROOF_NOTES.md#source-corrections) explain the
original errors, examples, and corresponding formal declarations.

The full `coqq` Dune build passes with all 70 Rocq sources. The new
`qft_main_global_index_bound` and `qft_main_input_local` proofs establish
that each rank-local source index is bounded and its initialized bit equals
`(i == 0)`. Both assumption reports say `Closed under the global context`.
Fresh checks of `qft_program_correct` and `qft_initialized_main_correct`
match their previous signatures and complete eight-foundation assumption
reports. No admission or new correctness axiom was introduced.

The [source checker](check_qft_source.py) passes against these rebuilt
libraries:

```sh
opam exec --switch=coqq -- dune build -j4
python3 src/example/distributive/check_qft_source.py
```

It checks the full endpoint, phase-helper, and main token signatures and
generates 296 operations from the actual source loops across all 17 rank
traces for `p=2,3,4,8`. Rocq checks 17 literal-source equalities and 17
concrete native-script equalities for arbitrary valid hardware allocations.
Each layout has eight H gates and 28 controlled phases; the teleport-hop
counts are respectively 8, 15, 18, and 35. The existing native program and
input-bit bridges are checked in the same run. The checker rejects stale
or changing source/build artifacts.

Negative checks confirm that it detects the two repairs: restoring F1's
old rank-zero formula fails the Rocq equality for `p=3`, rank zero;
removing F2's guard fails the full main signature. Both defective variants
were temporary files; the repository source remains the corrected program.

The audit covers accepted executions under the documented exact-gate,
ideal Bell-service, and data-observation allocation model. It does not claim
a certified isQ parser/compiler or equality of auxiliary runtime traces.

## Total Hoare correctness checkpoint

Date: 2026-10-06. The repository-wide build passes with all 70 Rocq sources,
using the `coqq` switch with OCaml 5.2.0:

```sh
opam exec --switch=coqq -- dune build -j4
```

All nineteen files in `classical` and `distributive` place their dependency
commands and shared `Set`/`Unset` flags in the file prelude. All source files
match the final Dune inputs and have compiled `.vo` artifacts. The distributed
framework remains in eight files; QFT is in its three files. See the
[semantic audit guide](QFT_PROOF_NOTES.md#semantic-audit-guide) for the source
mapping and precise program/specification boundary, and its Validation section
for the final 17-result theorem assumption audit.

The first module of [qft.v](qft.v), `DistributedQFTProgram`, now contains
all executable source definitions before the proof details: literal H/phase
matrices, both teleport endpoints, both rank loops, the actual `DL.Process`
and `DL.Program`, and the main/resource initializer. Exact script, process,
program-record, and initializer equalities connect this code to the existing
proof program. Checked source-occurrence lookups preserve gate powers,
endpoint direction, shared Bell IDs, and rank-local order.

`DistributedQFTSpecification`, immediately after the program, defines
mathematical input and output assertions independently of execution: a pure
data state and specified fresh Bell resources, and the corresponding
`F_8` output with input-bit reversal. The primary public result
`DistributedQFTProgramCorrectness.qft_program_correct` proves
`DistributedHoare.Network.derives true` for these assertions and the actual
`DL.Program`'s processes. Resource-only termination and the prepared-main
instance are also total network Hoare formulas.

The native proof uses network consequence and the framework's total
derivation, with the checked channel calculations supplying the quantum
assertion implication. The global ideal Bell-service initializer has its
own classical Hoare derivation. `qft_initialized_main_correct` composes it
with the native network using the sequence rule. The input/output state
equations are corollaries obtained from Hoare soundness, mass bounds, and
pure-projector saturation.

The final audit checks 17 results: four original source results, four raw
channel support results, four native Hoare results, the initializer, the
initialized-main triple, and three state corollaries. Every result reports
exactly the same eight inherited classical/real/memory foundation symbols
listed in [QFT proof notes](QFT_PROOF_NOTES.md#validation). The four original
source theorem signatures and complete assumption reports remain unchanged.
No new assumption, admission, or proof-level abort was introduced.

## Earlier reorganization checkpoint

Date: 2026-10-04. The full project build passed with all 67 Rocq sources:

```sh
opam exec --switch=rocq.9.1 -- dune build
```

All eight distributed topic files compile, including the independent local
and network calculi, their partial/total soundness and relative completeness,
sequentialization, auxiliary rules, and the teleportation and remote-CNOT
case studies. The public judgments `DistributedHoare.Local.derives` and
`DistributedHoare.Network.derives` were checked against their respective
`sound_complete` theorems.

Fresh assumption checks of both public completeness theorems,
`DistributedCorrespondence.denote_program_sequentialize`,
`DistributedMemoryReplay.global_step_memory_change_access`, and both
`DistributedProtocolCorrectness` theorems report only the inherited
real/choice/extensionality foundations and existing memory parameter `qreg.G`.
The source audit found no admissions, new axiom/parameter declarations, or
unfinished/debug proof commands in the reorganized or imported examples.

See [the complete validation record](../classical/VALIDATION.md) for the
67-source inventory, exact inherited assumptions, and historical checks.
[Coverage](README.md#coverage) and [proof notes](PROOF_NOTES.md#proof-gaps)
retain the mathematical boundaries and paper diagnoses. The reorganization
introduces no mathematical repair or extra assumption.
