# Reusable prompts for formalizing quantum program examples

These prompts capture the requirements established during the distributed QFT
development. They are instructions for a future formalization task; exporting
them does not start another example or certify any proposed proof.

Use the complete prompt below for a new task. Replace the angle-bracket fields
before sending it. The focused prompts are useful for continuing an existing
task; in a new conversation, include the project constraints and example brief
as well. All displayed Rocq formulas are schematic interfaces, not compiled
declarations for a new example.

## 1. Complete launch prompt

```text
Formalize <EXAMPLE_NAME> in the existing CoqQ repository and finish the proofs.

Example brief:
- Repository: /home/zhou/Desktop/CoqQ
- Source program and/or paper: <SOURCE_PATHS_AND_EXACT_PAPER_VERSION>
- Mathematical guide, if any: <GUIDE_PATH_OR_NONE>
- Target: <classical | distributive>
- Intended mathematical operation: <INDEPENDENT_MATHEMATICAL_SPECIFICATION>
- Required scope: <SIZES_DIMENSIONS_INPUTS_LAYOUTS_AND_OTHER_PARAMETERS>
- Correctness observations: <QUANTUM_OUTPUT_CLASSICAL_OUTPUT_SUCCESS_FAILURE>
- Source corrections: fix clear local bugs while preserving the intended
  algorithm; explain any change that affects its mathematical behavior.

Project constraints:
1. Read AGENTS.md and inspect the current workspace before editing. Stay on
   cqwhile+distributive. Never push. Preserve existing local modifications;
   do not reset, discard, or stash them to simplify the task.
2. Use the named coqq opam switch with ocaml-base-compiler.5.2.0 and the
   dependencies pinned by coq-mathcomp-quantum.opam. Inspect the actual toolchain
   and declarations; a guide's API examples or old environment report are not
   evidence that code works in this checkout. Reuse the switch if it exists.
3. Reuse the existing classical and distributive languages, semantics, Hoare
   calculi, and mathematical libraries. Prove genuinely missing helper lemmas.
   Do not introduce a replacement language or weaken the existing calculus.

Understand the program and mathematics first:
4. Explain the intended computation and correctness statement in ordinary
   mathematical language, then give a proof outline tied to source steps.
   Resolve composition order, tensor/register order, basis/bit order, control
   versus target, phase conventions, initialization, measurement, and final
   permutations before encoding the theorem. For a paper, verify its exact
   version, theorem hypotheses, and conventions against the actual source.
5. Audit source bounds, indices, branches, arithmetic, allocation, resource
   reuse, and communication. Check nonuniform layouts and boundary cases when
   relevant. Do not change an intentional gate or language construct merely
   because it looks unusual.
6. If there is a source bug, provide the complete corrected source. Mark each
   repair inline with the original incorrect command, the corrected command,
   the reason, and a concrete failing example. For a missing guard, show the
   original insufficient guard/unsafe path and the added check. Distinguish
   executable fixes from comment clarifications, and explain whether an edit
   is small locally but changes valid-input behavior. Preserve an original
   snapshot when available; never invent an archived original or textual diff.

Make the native program and specification easy to audit:
7. Put a compact, contiguous program-definition section near the beginning of
   the main example file, before proof infrastructure. It must visibly use the
   existing language.v constructors for gates, initialization, measurement,
   classical control, and, where applicable, communication and processes.
   Include the relevant gate definitions and endpoint code in this section.
8. For classical code, construct a ClassicalLanguage.command. For distributed
   code, construct actual DistributedLanguage.process values and a
   DistributedLanguage.program, discharging their well-formedness, finite-read,
   private-ownership, and point-to-point obligations. A separate ideal circuit
   or list of abstract actions is supporting mathematics, not the native
   executable program. Prove its connection to that program.
9. Keep source loops and operand choices recognizable. Explain static loop
   expansion, private counters, allocation adapters, and indexing if used.
   Prove lookup failures and incompatible instruction cases unreachable on the
   claimed source scope. Do not hide the whole program behind an opaque alias.
10. Immediately after the program definitions, give explicit mathematical
    preconditions, postconditions, and the main correctness formula. Define the
    desired transformation independently of execution. Do not define the
    advertised precondition as the program's weakest precondition, or define
    correctness as executing the program and obtaining whatever it produces.
11. State the primary theorem in the existing Hoare logic. The schematic forms
    are:

      CQHoare.derives true pre program post

    or, for a native distributed program:

      DistributedHoare.Network.derives true pre
        (DistributedLanguage.processes program) post

    The actual file must define properly typed assertions and the program.
    Semantic validity or an input/output channel equation alone is not the
    primary theorem. A new notation around such an equation is insufficient.
12. Put genuine input/resource requirements in explicit assertions where
    appropriate. Keep structural parameters, such as a valid register
    allocation or a declared oracle contract, precise and inspectable. They
    must not contain the algorithm's desired correctness equation. Prove
    initialization establishes the input assertion, including its data pattern
    and resources; equality between two copies of a compact initializer does
    not independently establish correspondence to the source initialization.

Choose a specification that fits this example:
13. Do not copy QFT-specific restrictions such as eight qubits, pure inputs,
    particular node counts, or probability-one success. State exactly the
    requested and actually proved parameter scope. Cover mixed states,
    classical mixtures, and entangled frames whenever the contract requires
    them; an isolated basis-vector calculation is not automatically enough.
14. For probabilistic or heralded algorithms, define the success event, failure
    event, unnormalized branch outputs, and success probability. Distinguish
    probability that the computation terminates from probability of obtaining
    the desired heralded result. A nontrivial total triple alone does not prove
    unconditional preservation of all input mass. Prove all-outcome termination
    and mass preservation for every admitted input under the full input
    contract; use top-to-top totality when that contract is top. Do not silently
    normalize away failure outcomes.
15. State whether the result concerns the full output, a reduced data register,
    a classical distribution, or selected branches. Define observations and
    ignored auxiliary memory explicitly. If reasoning from a selected matrix
    block to a full-memory assertion, prove the needed support and operator
    identities; the selected-block equality alone need not suffice.

Complete the proof using the existing logic:
16. Prefer compositional Hoare proofs: primitive rules, sequence, consequence,
    conditional rules, local protocol contracts, framing, loop invariants,
    rankings, and the appropriate network rules. Prove termination, ownership,
    resource preservation, and communication progress where needed.
17. Semantic calculations are allowed for quantum identities, assertion bounds,
    and other obligations. Existing soundness/completeness may be used when
    helpful. Report the method honestly: distinguish an explicit invariant
    proof from a derivation obtained via semantic calculations and relative
    completeness. Do not claim the latter is a new hand-written loop proof.
    Do not add a constructor that turns semantic validity into derivability.
18. Make direct input/output statements corollaries of the Hoare results using
    existing soundness where possible. Soundness supplies an expectation
    inequality; exact state/channel equality may additionally require an
    effect family, complementary bounds, mass preservation, or support/pure-
    projector saturation. Prove those steps rather than asserting equality
    from one lower bound. Cite any further semantic work that remains needed.
19. Finish without admit, Admitted, abandoned proof-level Abort commands, or
    new axioms filling correctness, mathematical, or helper-lemma gaps. Do not
    replace a missing lemma by a hypothesis,
    record field, oracle, or parameter that assumes the desired result. Genuine
    input contracts and explicitly justified mathematical hypotheses are
    allowed; list them accurately. Existing foundational assumptions must be
    reported rather than described as absent.

Establish source correspondence and present the finished development:
20. Provide a source-to-definition mapping covering every relevant loop bound,
    index, gate operand/parameter, branch, measurement/message/correction order,
    resource operation, and initializer. For corrected code, compare against
    the corrected source. Prove structural or semantic bridges for lowering,
    scheduling, and loop encoding. State explicitly which boundary is manual
    transcription, which is mechanically checked, and which is an abstraction.
21. Justify ideal services, exact arithmetic/gates, allocation/lifetime changes,
    ignored auxiliary states, and any other abstraction actually used. Track
    correlations and overwritten classical records where relevant. Do not
    claim full compiler/runtime equivalence from a data-marginal theorem.
    Add a reproducible source checker when useful; label an executable audit
    accurately instead of calling it a certified parser/compiler.
22. After the proof is complete, organize the new example into one to three
    clearly scoped .v files. A useful split is the public program/specification/
    main Hoare result, supporting mathematics, and optional protocol/resource
    proofs. Keep executable definitions together. Keep all Require/From Require
    commands and shared Set/Unset flags in the file prelude. Module-local
    Imports, notation, and scopes may remain at their module beginnings.
23. Write a concise human audit guide: where the native program is, what its
    pre/postconditions mean, why these match the intended algorithm, the exact
    main theorem and corollary names, source fixes, proof method, parameter
    scope, and actual model boundaries. Proof details may follow later.
24. Compile the changed proofs and dependencies, then the final reorganized
    repository, using:

      opam exec --switch=coqq -- dune build

    Audit the main results and critical source bridges with Check and Print
    Assumptions. Verify the final sources were built, not just scratch fragments
    or stale artifacts. If a source checker is supplied, demonstrate that it
    accepts the corrected source and rejects the original relevant defect.
25. Continue through implementation, complete proofs, final organization, and
    validation. Do not stop after a plan, mathematical guide, or compilable
    definitions. If a real obstacle remains, state the exact unresolved theorem
    and what is proved; never present an incomplete development as finished.

Final deliverables:
- Corrected and annotated source when a fix is necessary.
- One to three fully checked example .v files, reusing existing infrastructure.
- A primary Hoare theorem for the native program and requested state corollaries.
- A human audit guide and reproducible build/assumption/source checks.
- A concise report of what was proved, its scope, validation, and any real gap.
  Keep every modification local; never push.
```

## 2. Source understanding and correction

Use before implementation, or when the source correspondence is unclear.

```text
Audit <SOURCE> before formalizing it. Explain its computation, intended
mathematical specification, conventions, and a natural-language correctness
proof. Check every loop bound, index, branch, gate parameter, initialization,
resource lifetime, and communication order, including relevant boundary cases.

If a bug exists, provide the complete corrected source with inline original
wrong commands, corrected commands, reasons, and concrete counterexamples.
For a missing guard, show the original unsafe path. Explain the size and
behavioral impact of each change. Do not mistake unusual but valid syntax for
a bug, and do not silently substitute another algorithm.

Map the corrected source to the existing language.v definitions. Identify
proved bridges and modeling abstractions separately. Preserve a real original
snapshot if available. Continue with useful independent work if an intended
behavior is genuinely ambiguous; do not silently choose a different target.
Follow the project's branch, toolchain, preservation, and no-push constraints.
```

## 3. Make the native program and main Hoare formula reviewable

Use when definitions are scattered or the advertised result is only a circuit
or channel theorem.

```text
Reorganize <EXAMPLE> so a reader can immediately inspect its native program
and mathematical specification. Put the complete compact source-facing program
section together near the beginning, with explicit allowed language.v
constructors and relevant gates/endpoints. Expose the actual command or
process/program constructors rather than only an alias for an abstract model.

Immediately afterward, define independent mathematical input/output assertions
and the main existing Hoare correctness formula. For classical code use
CQHoare.derives; for distributed code use DistributedHoare.Network.derives on
the processes of the actual DistributedLanguage.program. Select the required
correctness mode explicitly. Do not advertise pre := wp(program, post) as an
independent specification.

Explain in mathematical language why the program matches <SOURCE> and why the
assertions express <INTENDED_RESULT>. Put genuine resources in the contract
and prove initialization establishes it. Preserve proved connections to the
supporting model and give exact theorem names. Do not claim this reorganization
alone completes any missing correctness proof. Follow the project constraints.
```

## 4. Finish the Hoare proof and semantic corollaries

Use after the native program and independent specification are fixed.

```text
Finish <MAIN_HOARE_THEOREM> for <NATIVE_PROGRAM> and the agreed explicit
pre/postconditions. Prefer the existing primitive, sequence, consequence,
conditional, frame, invariant, ranking, and network rules. Prove the necessary
well-formedness, resource, termination, and communication obligations.

Use semantic/operator calculations when they genuinely discharge obligations;
if relative completeness supplies the derivation, explain that proof route.
Do not weaken the target, replace the program, assume a desired channel
equation, or add a semantic-validity constructor to the logic.

Derive <REQUESTED_OUTPUT_COROLLARIES> through Hoare soundness and the additional
mass/support/effect arguments needed for exact equality. For a heralded
algorithm, keep unnormalized success and failure outputs and distinguish
termination from success probability. Prove all-outcome termination for the
admitted inputs, rather than requiring an unjustified global top-to-top
statement. Do not impose QFT's pure-input or
probability-one-success pattern on another algorithm.

Complete all proofs without admissions, proof-level aborts, or new axioms for
missing correctness, mathematical, or helper lemmas. Compile with
opam exec --switch=coqq -- dune build and audit the
finished theorem signatures and assumptions. Report actual remaining gaps
precisely rather than claiming completion. Keep changes local and never push.
```

## 5. Independent semantic audit

Use for a review of whether the formalization proves the intended claim.

```text
Review <EXAMPLE> primarily for semantic fidelity. Read <SOURCE>, the native
program, the actual Hoare formula, supporting correspondence lemmas, and the
human audit notes. Do not judge success merely from successful compilation.

Check that the native program uses the existing language and corresponds to
the corrected source, including all bounds, indices, orders, controls, phases,
registers, resources, and initialization. Check what is actually observed:
full state, reduced data, classical output, or selected measurement branches.
Inspect reused registers, overwritten stores, entanglement, and any ideal
service/allocation abstraction.

Check that the pre/postconditions are independent mathematical specifications,
that the main result is the existing Hoare judgment for that exact program,
and that no assumption secretly supplies the desired algorithmic identity.
Check the claimed parameter/input scope and success-versus-termination claim.
Verify that proposed state equalities follow from the actual Hoare result and
the additional bounds or support facts cited. Distinguish kernel-checked
proofs from mathematical notes, executable audits, and unproved guide code.

Report concrete discrepancies with file/declaration references and their
effect on the main claim. Keep this review read-only unless fixes were also
requested. Follow the project's branch, toolchain, and no-push constraints.
```

## 6. Consolidate and validate the completed example

Use once the proofs are complete; moving files is not a substitute for closing
proof obligations.

```text
Confirm that <EXAMPLE>'s requested Hoare results and correspondence proofs are
complete, without admissions or new correctness assumptions. Then consolidate
the new example into one to three .v files with clear scopes and a compact
public native-program/specification section. Preserve the established public
statements and meaningful source bridges. Do not refactor unrelated examples.

Move all Require/From Require commands and shared Set/Unset flags to each
file's prelude. Keep module-local Imports, notation, and scopes at module
beginnings. Update build dependencies and cross-references as necessary.

Build the final repository with opam exec --switch=coqq -- dune build. Audit
the principal theorems and critical source bridges using Check and Print
Assumptions, and compare earlier signatures/reports where applicable. Verify
current sources and compiled artifacts correspond. Distinguish the language's
Abort constructor from an abandoned proof-level Abort command when scanning.

Update the audit guide and validation record with actual results, exact public
theorem names, source-fix markers, observations, parameter scope, inherited
foundations, and model boundaries. Do not describe inherited classical
foundations as axiom-free. Report completion only after the final layout has
been checked. Stay on cqwhile+distributive; never push.
```

## Example brief for a future QSVT task

This is a suggested way to fill the launch prompt, not an instruction to start
QSVT and not a claim that its guide has been machine-checked:

```text
EXAMPLE_NAME: exact QSVT
SOURCE_PATHS_AND_EXACT_PAPER_VERSION:
  1806.01838v1.pdf; verify the actual version and the guide's theorem references
GUIDE_PATH_OR_NONE:
  qsvt_rocq_coqq_full_proof_en_zh_v2.md
TARGET: classical
INDEPENDENT_MATHEMATICAL_SPECIFICATION:
  The exact polynomial singular-value transformation specified in the guide,
  defined independently of the program and checked against the chosen paper.
SIZES_DIMENSIONS_INPUTS_LAYOUTS_AND_OTHER_PARAMETERS:
  State and verify the compatible dimensions, encoding/isometry contracts,
  polynomial hypotheses, nominal degree/parity, and requested input scope.
QUANTUM_OUTPUT_CLASSICAL_OUTPUT_SUCCESS_FAILURE:
  Quantitative total Hoare correctness of the native heralded program;
  explicitly specified success/failure outputs and exact success mass,
  with a separate all-outcome termination/mass-preservation result.
```

The QSVT guide explicitly marks its new Rocq declarations as uncompiled.
Verify its mathematics and implement/check the actual declarations; exporting
this brief does not change that status. A selected matrix-block identity must
not silently replace the stronger support and program-correctness obligations.

## Repository entry points

| Purpose | Files |
| --- | --- |
| Project constraints and dependencies | [AGENTS.md](AGENTS.md), [coq-mathcomp-quantum.opam](coq-mathcomp-quantum.opam) |
| Classical syntax and calculus | [language.v](src/example/classical/language.v), [hoare.v](src/example/classical/hoare.v) |
| Distributed syntax and calculus | [language.v](src/example/distributive/language.v), [hoare.v](src/example/distributive/hoare.v) |
| Existing example/library map | [classical README](src/example/classical/README.md), [distributive README](src/example/distributive/README.md) |
| Worked source/Hoare audit | [QFT program](src/example/distributive/qft.v), [QFT notes](src/example/distributive/QFT_PROOF_NOTES.md) |
| Executable source-audit example | [check_qft_source.py](src/example/distributive/check_qft_source.py) |

For distributed serialization, inspect the actual types: the existing
`Network.derives_translate_sound` yields classical semantic validity, not
directly a `CQHoare.derives` proof. Local operational soundness requires the
statement's well-formedness. Use the current source declarations when composing
these bridges; the schematic prompt formulas do not replace type checking.
