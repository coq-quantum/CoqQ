# Distributed QFT program and semantic audit

The main result is a total-correctness Hoare formula for the native distributed
program modeling [qft.isq](../../../qft.isq), after its rank-zero index and allocation
guard corrections. The physical program theorems cover the literal `n = 8`
main for every accepted node count: `p = 2, 3, 4, 8`. Because the source omits
the final reversal, its circuit is `D = F composed with S`, where `F` is the
repository's Fourier transform and `S` reverses the input tuple.

Open [qft.v](qft.v) at `DistributedQFTProgram`: its first section gives the
native endpoint statements, the two rank-local source loops, the guarded
process, and main initialization together. Immediately afterward,
`DistributedQFTSpecification` defines the mathematical input/output predicates
and the correctness formulas in `DistributedHoare.Network.derives`.
The semantic audit guide below
explains their source correspondence and the correctness statements in
`DistributedQFTProgramCorrectness`. The later sections explain the mathematics
and proof architecture. The model uses exact gates, private allocated
registers, and fresh ideal Bell resources. It does not certify an isQ
parser/compiler translation or the implementation of QMPI's EPR service.

## Semantic audit guide

### Match the source to its formal definitions

Open [qft.isq](../../../qft.isq) beside the first module of [qft.v](qft.v),
`DistributedQFTProgram`. Search for the declaration names in this table;
they remain useful when line numbers change. `qft_rank_script` writes the
rank-local source loops directly. Its endpoint scripts use the allowed
`DL.Atomic`, `DL.Sequence`, `DL.Alternative`, `DL.Input`, and `DL.Output`
constructors; `qft_process` explicitly constructs a `DL.Process`.
`LocalStatement` and `LocalCommunication` delimit finite local segments,
rather than adding another execution semantics.
`literal_instruction_script` visibly selects Hadamard or `controlled_R power`,
whose exact phase matrix is defined in the same block; lookup supplies their
typed registers, rather than choosing the gate.

The source loops are a manual transcription of isQ. Structural equalities
connect this code to the existing proved program; they do not compare a
parsed isQ syntax tree. Use [qft_model.v](qft_model.v) for the supporting
layout, typed allocation, and finite source certificates.

The source to compare is the corrected repository-root `qft.isq`, including
its `FIX F1` conditional and `FIX F2` guard. Correspondence here concerns the
accepted execution's gates, ordered endpoint messages, logical data locations,
and initialized data state, under the stated allocation and Bell-service
model. Source declarations of temporary qubits are represented by allocated
register slots. In particular, the model permits an arbitrary old destination
state where the source declares a zero-initialized `anc`, as specified by the
[isQ allocation rule](https://www.arclightquantum.com/isq-docs/latest/grammar/#primitive-types);
the receiver's SWAP
proof shows that this state moves into disposable Bell memory and does not
affect the reduced data output. The theorem therefore covers the source's
zero-initialized case without specifying its full auxiliary allocation/reset
trace.

| Source to inspect | Formal declarations | Semantic check |
| --- | --- | --- |
| `main`: `n = 8`, normal/left widths, both early-return guards | The `p`, `valid_source_layout 8 p`, and `physical_memory` parameters of `DistributedQFTProgram` in [qft.v](qft.v); `normal_size`, `main_accepts`, `main_accepted_nodes` in [qft_model.v](qft_model.v) | `m = ceil(8/p)` and `left = 8-(p-1)m`; execution reaches allocation exactly for `p` in `{2,3,4,8}`. Error printing and rejected-layout return behavior are not part of the quantum correctness theorem. |
| Rank-local `q[i]`, `q.length`, and the rank-zero index correction | The literal `index` in `qft_remote_target` in [qft.v](qft.v); `width`, `offset`, `global_index`, `cross_index`, `phase_parameter` in [qft_model.v](qft_model.v) | Concatenate rank blocks in increasing rank/local-index order. Rank zero uses `left+(ir-1)m+i`, while other ranks use `(ir-rank)m+i`. The remote power `index-j+1` is the global target/control distance plus one. |
| The earlier-qubit loops over `ir`, `i`, and `j` | `qft_remote_target`, `qft_rank_script` in [qft.v](qft.v) | Higher origins descend from `np-1` to `rank+1`; their local targets descend from `m-1` to zero. A rank receives, applies phases with its local controls in ascending order, then forwards or returns the target. |
| The current-node loop, including H before its phases | `qft_own_target`, `qft_rank_script` in [qft.v](qft.v) | Local targets descend. Each receives H, then phases with exactly the smaller local indices and literal power `i-j+1`. Nonzero ranks send the target down and receive its return from zero. |
| `R(k)` and `ctrl R(..., q[j], target)` | `controlled_R`, `literal_instruction_script`, `source_operation_script` in [qft.v](qft.v); typed operands from `compile_source_step` in [qft_model.v](qft_model.v) | The visible native statement uses Hadamard for H and `controlled_R power` for a phase. The latter multiplies only the control/target `11` basis value by `exp(2 pi i / 2^power)`. The control is local `q[j]`; the target is its current data slot or received `anc`. |
| `send_target`, neighbor forwarding, and the return from zero | `route`, `scheduled_target`, `natural_schedule`, `joint_schedule`, `source_eight_joint_expansion` in [qft_model.v](qft_model.v) | An origin `h>0` follows `h -> h-1 -> ... -> 0 -> h`. Combining a matching send/receive into a `TransferStep` expands back to the original source action list. Every target returns to its original data slot. |
| `teleport_send` and `teleport_recv` | `native_send_script`, `native_receive_script`, `native_correction` in [qft.v](qft.v) | Read the actual allowed constructors for CNOT/H/measurement, bit output/input, conditional X/Z, and SWAP together. A teleport is not a primitive assumed to be the identity. |
| Repeated classical tag `88` and rank-local variables | `qft_process` in [qft.v](qft.v); `bit_channel`, `channel_endpoints`, `stage_variable`, send/receive bit variables in [qft_model.v](qft_model.v) | Channels encode sender, receiver, and tag. Both correction bits use the same endpoint channel in order. Private integer counters control the finite communication script; payload variables are Boolean. |
| `anc` declared inside the `ir` loop and fresh `pair` variables | `DataWire`, `AncillaWire`, `target_wire`, `physical_memory`, `compile_source_step` in [qft_model.v](qft_model.v) | An ancilla slot is indexed by `(rank, origin)`, matching the outer-loop declaration and reuse across its `i` iterations. Each transfer has distinct Bell halves. The allocation interface supplies valid registers and disjoint process regions. |
| Zero allocation and `X(q[0])` at every rank | `qft_main_input`, `qft_main_data_index`, `qft_main_input_local`, `qft_initialize`, `prepare_epr`, `prepare_epr_resources`, `qft_main` in [qft.v](qft.v) | `qft_main_input_local` proves that each rank-local bit `i` has value exactly `(i == 0)`, including the shorter rank-zero block. Bell initialization is the explicit ideal resource preparation before private processes execute. |

`source_operation_script` uses `DistributedQFTSourceIndex.operation_index`
in [qft_model.v](qft_model.v) to align a source operation with its existing
typed allocation. For a phase, the key retains rank, target, control, and
the explicit power. For a send it retains `(target, sender, receiver)`;
the matching receive names that same directed transfer.
`transfer_operation_index` identifies their shared allocation index.
`source_eight_operation_lookup` proves that every source-used index is in
bounds, selects exactly the intended step, and has a unique matching
occurrence. `source_eight_operation_indices` preserves the rank-local
order of those occurrences. Thus lookup assigns the correct registers and
Bell resource slot while `literal_instruction_script` uses the source's
explicit matrix and power. A missing index or incompatible typed instruction
cannot occur in an accepted source script. `direct_instruction_script` is
used to prove the bridge to the earlier compiler.

### Check the gates and the teleport order

The intended interpretation of `R(K)` is
`diag(1, exp(2 pi i / 2^K))`. isQ's zero-qubit `GPhase(theta)` acquires a
relative phase when controlled; the further `ctrl R` applies it only when
both the control and target are one. This agrees with the official
[gate definitions](https://www.arclightquantum.com/isq-docs/latest/gate/)
and [QFT source example](https://www.arclightquantum.com/isq-docs/latest/examples/hsp/).
For global target `k` and control `j<k`, the modeled angle is
`2 pi / 2^(k-j+1)`, with a positive sign. There is no final reversal SWAP
in the QFT circuit; the SWAP inside `teleport_recv` serves only to move the
received state into the destination slot.

Read the two teleport endpoints separately:

- Sender: obtain a Bell half; CNOT from data to that half; H on data;
  measure the Bell half as `x`; send `x`; measure data as `z`; send `z`.
- Receiver: obtain the other Bell half; receive `x` and conditionally apply
  X; receive `z` and conditionally apply Z; SWAP the corrected Bell half
  into `anc` or `q[i]`.

`native_send_script` and `native_receive_script` display these local orders
directly; their structural bridge also matches `lower_transfer`. After the
first rendezvous,
the sender's z measurement and the receiver's X correction may occur in
either global order: they belong to different private endpoints. The
canonical command `call_serial` in [qft.v](qft.v) puts the z measurement
before X; it is connected to the distributed process semantics by proved
commutation, rather than by changing either endpoint's source order. Its
store updates retain the actual reused correction variables. The old
destination state need not be zero: SWAP moves it into the disposable Bell
register, and the data theorem reduces away such registers.

### Identify the program and its correctness statement

In `DistributedQFTProgram` at the beginning of [qft.v](qft.v),
`qft_rank_script` assembles the two source loops from native endpoint
statements. `qft_process` explicitly constructs each rank's `DL.Process`:
local initialization, a private integer counter, guarded communications,
and their local continuations. `qft_program` explicitly packages this
family into `DL.Program`; its well-formedness, finite-read, privacy, and
point-to-point obligations are discharged. `qft_main` adds the visible
`qft_initialize` prefix before successful execution of that program.

The structural bridge is `qft_rank_scriptE`, `qft_processE`, and
`qft_programE`, followed by `qft_initializeE` and `qft_mainE` for the main
prefix. These equalities connect the directly written code to
`DistributedQFTInstance.source_program` and its initializer in
[qft_model.v](qft_model.v). That existing instance compiles
`joint_schedule` to `source_instructions`, lowers them to
`source_network_actions`, and projects them to `source_processes`.
The new code is not a public alias for that instance: it constructs the
rank-local syntax and native process, and then proves that they agree.
Neither program is the separate ideal logical circuit `logical_program`.

The source-main initialization has an additional independent check:
`qft_main_global_index_bound` establishes that each local data index denotes
a global coordinate below eight, and `qft_main_input_local` proves

```coq
tnth qft_main_input (qft_main_data_index (rank := rank) i)
  = ((i : nat) == 0)%N.
```

Thus the basis tuple is precisely zero allocation followed by `X(q[0])`
at every rank. This statement is proved for every accepted layout from the
layout's ownership and positive-width facts. `qft_initializeE` itself equates
the two compact initializer definitions; the input-bit theorem supplies
their independent connection to the source's initialized data pattern.

In the supporting `DistributedQFTProgramSemantics` module of [qft.v](qft.v),
`qft_channel s` sums the cq denotation of
`successful_sequentialize(processes(qft_program))` over all actual final
classical stores, for initial store `s`; `qft_main_channel` does the same
for `qft_main`. Existing distributed semantics and sequentialization
justify this interpretation. No unique-enabled-rendezvous premise is
used. The proof-side `source_program_instruction_denote` is the exact
native-kernel bridge to the instruction sequence, including measurements
and counter assignments; the structural equalities transfer its meaning
to this source-facing code.

The primary specification is in `DistributedQFTSpecification`, immediately
below the program definitions. Let `D = tuple_fourier 8 composed with reversal 8`.
For a normalized vector `psi`, `prepared_assertion memory psi` is the projection
onto the intersection of:

- the subspace where the native data register is exactly `|psi><psi|`;
- every used transfer slot's specified Bell-pair subspace.

`qft_output_assertion memory psi` is the lifted data effect `|D psi><D psi|`.
Auxiliary memory and classical records are unrestricted. Neither assertion
uses a program execution or a weakest precondition.

`qft_correctness_formula memory psi` is the existing total distributed Hoare
judgment, proved by `DistributedQFTProgramCorrectness.qft_program_correct`:

```coq
DistributedHoare.Network.derives true
  (prepared_assertion memory psi)
  (processes (qft_program memory))
  (qft_output_assertion memory psi).
```

Thus the theorem's program is the actual `DL.Program` displayed above, and
`true` selects total correctness. Fresh Bell resources are part of the
mathematical precondition, rather than an extra premise of the theorem.
`qft_program_total` also proves the resource-only triple with identity as its
postcondition, allowing arbitrary data and auxiliary memory.

`qft_main_correctness_formula` and `qft_main_correct` specialize the native
network triple to `qft_main_input`. The initializer establishes `qft_main_pre`;
`qft_initialized_main_correct` then derives the unconditional Hoare triple
for the global prefix followed by the native network, using sequence
composition. The prefix models the external ideal Bell service and is
explicitly a classical command, rather than a private distributed process.

The proof uses the network consequence rule and the framework's total
network derivation, with its generated tail invariant and remainder ranking.
The checked physical channel and termination lemmas establish the assertion
implication used by consequence. Initialization uses consequence and the
primitive initialization/unitary/sequence derivations; the main composition
uses sequence. This is a Hoare derivation with semantic calculations for its
quantum assertion bounds, rather than a new hand-written QFT-stage invariant.

The state results are corollaries of Hoare soundness, probability-mass bounds,
and pure-projector saturation. `qft_program_state_correct` gives the exact
data marginal when its explicit input assertion holds with full mass.
`qft_initialized_main_state_correct` gives, for arbitrary classical-quantum
input, successful output mass equal to input mass and data state

    mass(input) * |QFTbv(reverse qft_main_input)><QFTbv(reverse qft_main_input)|.

`qft_initialized_main_physical_state_correct` gives the corresponding
single-store density-operator statement. A normalized input has output
probability one. These corollary proofs use the Hoare theorems, rather than
calling the old output channel equality again.

The main input tuples are `10001000`, `10100100`, `10101010`, and `11111111`
for `p=2,3,4,8`, respectively. The no-final-SWAP convention remains `D=F S`.
The retained raw channel calculations are supporting lemmas in
`DistributedQFTProgramSemantics`; they are not the primary public correctness
specification.

### Check the abstractions before applying the result

The correspondence uses the following explicit abstractions:

- **Finite loops:** the visible `qft_rank_script` statically unrolls the
  source loops and is tied to `rank_source` and `joint_schedule` by exact
  structural equalities. The checked source certificates cover all accepted
  layouts of the literal eight-qubit main. Generic Fourier and network
  lemmas do not make the physical source theorem general in `n`.
- **Bell service:** `create_epr(...,99,...)` consumes the distinct ideal
  Bell pair assigned to its transfer. The visible `prepare_epr` uses global
  Initialize/H/CNOT before the private distributed program, and
  `qft_initializeE` ties it to the existing resource initializer. No
  implementation of the QMPI EPR handshake, delivery, or failure behavior
  is verified.
- **Allocation:** `physical_memory` gives static native register labels
  for data, ancillas, and Bell halves, with enough space and disjoint
  endpoint regions. Dynamic allocation/deallocation is abstracted; the
  theorem observes restored data, not the lifetime or final contents of
  every temporary register. Unused local-step Bell slots in the uniform
  allocation family are not consumed resources.
- **Exact operations and messages:** phases are exact real values and
  correction messages use the distributed language's rendezvous semantics.
  Floating-point rounding, physical gate errors, asynchronous network
  implementation details, and error printing are outside the result.
- **Source translation:** there is no certified raw-isQ parser, compiler,
  or QMPI-to-Rocq translator here. The mapping above is the inspectable
  modeling argument; the subsequent native program and correctness proof
  are mechanically checked.

The initialized-main Hoare theorem has only the accepted-layout and hardware
allocation parameters. Its state corollaries allow an arbitrary initial
classical-quantum state, or a store and density operator. They do not ask the
caller to assume the Fourier equation or successful execution.
The foundation assumptions and build checks are listed under Validation.
The remaining sections develop the mathematical explanation and the proof
architecture for readers who want to inspect how the result is established.

## File and module navigation

The development is organized into three files. The named Rocq modules and
their theorem interfaces are retained across this file consolidation.
The dependencies run from the model to the teleport proofs, then to complete
program correctness; the final file also imports the model directly.

| File | Scope and modules |
| --- | --- |
| [qft_model.v](qft_model.v) | Layout and source certificates (`DistributedQFTSchedule`, `DistributedQFTSource`, `DistributedQFTNames`, `DistributedQFTLocations`, `DistributedQFTInterleaving`, `DistributedQFTSourceIndex`); Fourier algebra and logical circuit (`DistributedFourierAlgebra`, `DistributedQFT`); finite network, lowering, and physical allocation (`DistributedFiniteTrace`, `DistributedQFTLowering`, `DistributedQFTInstance`). |
| [qft_teleport.v](qft_teleport.v) | Teleport state identities (`DistributedQFTTeleport`); Bell preparation and support (`DistributedQFTBell`, `DistributedQFTBellSupport`); native register reduction (`DistributedQFTReduction`); local processes, channels, and literal isQ transfer (`DistributedQFTTeleportProcesses`, `DistributedQFTTransferCorrectness`, `DistributedQFTISQTransfer`). |
| [qft.v](qft.v) | Native executable program and explicit Hoare formulas first (`DistributedQFTProgram`, `DistributedQFTSpecification`); gate/resource/execution calculations (`DistributedQFTCommutation`, `DistributedQFTComposition`, `DistributedQFTTransferKernel`, `DistributedQFTStepSemantics`, `DistributedQFTResources`, `DistributedQFTExchange`, `DistributedQFTCanonical`, `DistributedQFTCorrectness`, `DistributedQFTProgramSemantics`); concrete predicate support and Hoare derivations (`DistributedQFTPreparedProjection`, `DistributedQFTHoareNetwork`, `DistributedQFTInitializationHoare`); soundness-based state extraction (`QFTHoareExtraction`); primary native Hoare results and state corollaries (`DistributedQFTProgramCorrectness`). |

The final program entry point is:

```coq
From quantum.example.distributive Require Import qft.
Import DistributedQFTProgram DistributedQFTSpecification DistributedQFTProgramCorrectness.
```

For a program audit, read `DistributedQFTProgram` at the start of `qft.v`,
then the four `qft_program_*` / `qft_main_*` results in
`DistributedQFTProgramCorrectness` at its end. The middle of `qft.v`
contains their supporting proofs. The layout, allocation, and Fourier
circuit are in `qft_model.v`; reusable teleport and reduction proofs are
in `qft_teleport.v`.

## What the program computes

Let `p = np`, `m = ceil(n/p)`, and `left = n - (p-1)m`. Rank zero owns `left`
qubits and every other rank owns `m`. A valid layout satisfies `p >= 2`,
`m >= 1`, and `1 <= left <= m`. The physical global position of local qubit
`i` on rank `r` is

    g(0,i) = i,
    g(r,i) = left + (r-1)m + i,  for r > 0.

Concatenate the arrays in increasing rank order and increasing local index
order. This physical order is the tuple order used below. The existing
classical formalization treats its first tuple bit as most significant;
isQ's displayed QFT circuit runs in the reverse physical direction.

The source processes global target positions `k` from `n-1` down to zero.
For each target it applies a Hadamard, then controlled phases with every
control `j < k`. Their order within a target may vary by rank, because all
these phases are diagonal and commute. The gate is

    CP(k,j)|b> = exp(2 pi i b[k] b[j] / 2^(k-j+1)) |b>.

The routine `R(K)` implements `diag(1, exp(2 pi i / 2^K))`. Its nested
`ctrl GPhase` is intentional: `GPhase(theta)` has zero quantum arguments,
and controlling it gives the one-qubit relative-phase gate. A further
control gives `CP`. This interpretation follows the official
[isQ gate definitions](https://www.arclightquantum.com/isq-docs/latest/gate/)
and [QFT example](https://www.arclightquantum.com/isq-docs/latest/examples/hsp/).

Let `F` be `ClassicalFourier.tuple_fourier n` and `S` be its bit-reversal
unitary. The physical descending circuit `D`, without a final SWAP, is

    D = F composed with S.

Thus its action on a physical computational basis tuple `b` is
`QFTbv(reverse b)`. It does not equal `F` in this tuple convention. If physical
indices are interpreted as little endian instead, the standard little-endian
Fourier transform is `S F S` and the omitted final output reversal gives
the same `D`. Correctness must state its chosen ordering explicitly.

The main routine initializes one bit on every rank: the call `X(q[0])`
executes at every process. It therefore prepares the basis string whose
ones are exactly the first positions of the rank blocks. The reusable data-channel
theorem covers arbitrary input operators under the fresh-resource contract;
the main theorem specializes it to this particular basis state.

Zero allocation followed by these local X gates is represented by the
compact initializer `CL.Initialize data_register |main_input>`. Every accepted
rank has positive block width, by `left_positive` and `normal_positive`.
Its local `q[0]` is global position `offset(L,r)`. These positions are distinct:
`owner_global_index` with local index zero identifies the owner of that
position as `r`. Consequently, bit `k` is true exactly when there exists a
rank `r` with `k = offset(L,r)`, which is the definition of `main_input`.
Writing tuples in global order from position zero through position seven gives:

| Ranks `p` | Positions initialized to one | `main_input` |
| --- | --- | --- |
| 2 | 0, 4 | `10001000` |
| 3 | 0, 2, 5 | `10100100` |
| 4 | 0, 2, 4, 6 | `10101010` |
| 8 | 0, 1, 2, 3, 4, 5, 6, 7 | `11111111` |

Measuring that ideal final basis-input Fourier state in the computational
basis gives probability `1/2^n` for each global output string, hence `1/256`
for the literal eight-qubit main. This sampling check cannot establish the
phase angles: the original erroneous rank-zero phases also leave those
basis-input output magnitudes uniform. The required correctness statement
therefore identifies the quantum state/channel, including its phases.

## Source corrections

The repository-root [qft.isq](../../../qft.isq) is the complete corrected
program. Its comments mark the two executable repairs as `FIX F1` and
`FIX F2`, and the output-location wording as `CLARIFICATION C1`. These are
small local changes: one rank-zero index override and one early-return guard.
They preserve the source's distributed routing and no-final-SWAP convention.

| Marker in `qft.isq` | Original error | Correction | Formal counterpart |
| --- | --- | --- | --- |
| `FIX F1` | `index = (ir-rank)*nqubit_normal+i` also used a full normal block at rank zero, even when its actual block was shorter. | At rank zero, set `index = nqubit+(ir-1)*nqubit_normal+i`. | The literal conditional in `DistributedQFTProgram.qft_remote_target`; `DistributedQFTSchedule.cross_index`, `cross_index_distance`, and `phase_parameter`. |
| `FIX F2` | Checking only `np >= 2` allowed an empty or negative rank-zero array, followed by `X(q[0])`. | Reject `nqubit_left < 1` before allocating the array. | `DistributedQFTInstance.main_accepts_layout` proves equality with `valid_source_layout`; `main_accepted_nodes` proves the accepted set is exactly `{2,3,4,8}`. |
| `CLARIFICATION C1` | The comment "result is always produced at node 0" could suggest that data remains there. | Explain that node zero applies the final phases and the next receive returns the state to its original owner. This is a comment correction. | `route` ends with `(0, origin)` for every nonzero origin; `source_eight_locations_return` proves restoration of the data slots. |

The original cross-node expression was `(ir-rank)m+i`. It measures the
target's position relative to the current rank's block start. It is correct
for `rank > 0`, but rank zero has a shorter block when `left != m`. There
the expression must be

    left + (ir-1)m + i.

Subtracting the local control position `j` and adding one then gives the
intended gate parameter `g(ir,i)-g(rank,j)+1`. The old expression overcounts
the rank-zero distance by `m-left`; all rank-zero controlled phases on
transported qubits then have the wrong angle.

For the literal main value `n=8`, valid nonempty layouts have
`p in {2,3,4,8}`. With `p=3`, `m=3` and `left=2`, so the bug changes every
cross-node phase applied at rank zero by a factor of one half in its angle.
For example, take `ir=1`, `i=0`, and `j=0`. The target is global qubit 2
and the control is global qubit 0. The original index was 3 and used `R(4)`
with angle `pi/8`; the corrected index is 2 and uses the intended `R(3)`
with angle `pi/4`.
For `p=5`, rank zero has zero qubits; for `p=6` or `p=7`, its computed array
length is negative. With `p>8`, it is again nonpositive. The condition
`np >= 2` alone therefore does not justify allocation or `X(q[0])`.
A second guard must reject `left <= 0` before allocation. The existing
`np < 2` guard already excludes the single-node case.

The source comment that the result is always produced at node zero refers
to the last point at which a transported qubit receives its phase gates.
The subsequent return teleport restores it to its original owner's array
slot. No output data is permanently gathered at node zero.

### Check the corrected file against the native program

The reproducible [source checker](check_qft_source.py) reads the current
repository-root `qft.isq`, rather than a separate copy of its loops:

```bash
opam exec --switch=coqq -- dune build -j4
python3 src/example/distributive/check_qft_source.py
```

It ignores comments and whitespace, checks the complete token signatures of
`teleport_send`, `teleport_recv`, `R`, and `main`, and interprets the actual
`qft` body with signed, end-exclusive loop ranges as defined by the
[isQ for-loop grammar](https://www.arclightquantum.com/isq-docs/latest/grammar/#for-loop).
Matched send/receive
endpoints determine each traveling qubit's logical identity and physical
carrier; the checker verifies that every data qubit returns to its original
slot. Unsupported source constructs cause the audit to fail.

For every rank of all four accepted layouts, it generates a literal ranked
operation list from that source interpretation and asks Rocq to prove equality
with `DistributedQFTSource.rank_source` by computation. These 17 rank traces
check every Hadamard, phase operand and power, teleport direction, and local
operation order. `qft_rank_script_source`, `qft_rank_scriptE`, and
`qft_programE` connect those source lists to the directly written native
scripts and actual `DL.Program`. The generated proofs also check a concrete
native-script equality for each rank, for every valid hardware allocation.
The source guard, input-bit, and phase-distance certificates above separately
justify the accepted layouts, initialized data pattern, and angle formulas.

The checker uses Python's standard library and the existing `coqq` proof
libraries; generated proof files are temporary. Its executable parser is an
audit tool, not a certified isQ compiler. The exact correspondence claimed
here has the data-observation, ideal Bell-service, exact-gate, and allocation
scope explained in the semantic audit guide.

## Why teleportation preserves the computation

For an origin rank `h > 0`, each of its qubits takes the route

    h -> h-1 -> ... -> 1 -> 0 -> h.

Before the first hop, the origin applies its Hadamard and phases controlled
by its own smaller local indices. At each lower rank, the received qubit is
temporarily held in `anc`; that rank applies phases controlled by all its
local data qubits. Rank zero then returns the result directly to the origin.
Every global lower control is visited exactly once.

Each teleport consumes a fresh independent Bell pair. The sender applies
CNOT from the data qubit to its Bell half, applies H to the data qubit,
measures its Bell half to obtain `x`, and measures its data qubit to obtain
`z`. It transmits `x` before `z`. The receiver applies X according to `x`,
then Z according to `z`. For each result pair the existing operator lemma
`DistributedProtocolQuantum.teleport_branch_correct` states

    branch(z,x) composed with resource = (1/2) embed(z,x).

Consequently, every branch leaves the receiver holding exactly the input
data state, with branch probability `1/4`; the source registers only retain
the measured basis values. This is an operator equation, so tensoring it
with an identity proves the same property when the data qubit is entangled
with the rest of the quantum memory. Summing the four density-operator
branches yields the identity channel on the relocated logical data. A
proof restricted to an isolated one-qubit vector would be insufficient.

The receiver's SWAP moves the corrected state from its Bell half to `anc`
or the destination `q[i]`. It moves the destination's old state to
the disposable Bell-half register. Reusing `anc` across successive source
qubits is therefore sound; reusing a consumed Bell pair is not sound.
The resource contract supplies a distinct Bell pair for every hop.
The SWAP proof allows the old destination state to be entangled with a
separate frame or correlated with previous classical measurement records;
it does not require that destination to be reset to zero.

For every valid source layout, including a shorter rank-zero block, there are
`m(p-1)(p+2)/2` teleport hops, that many Bell pairs, and twice as many
transmitted correction bits. Local target qubits on rank zero do not travel.
The native certificate `source_eight_resource_count` checks the literal
eight-qubit schedules:

| Ranks `p` | Normal width `m` | Rank-zero width `left` | Teleport hops / Bell pairs | Correction-bit messages |
| --- | --- | --- | --- | --- |
| 2 | 4 | 4 | 8 | 16 |
| 3 | 3 | 2 | 15 | 30 |
| 4 | 2 | 2 | 18 | 36 |
| 8 | 1 | 1 | 35 | 70 |

## Resource creation and the language boundary

The existing distributed language has private local initialization,
unitaries, measurements, assignments, and classical two-party rendezvous.
It does not contain an external quantum-network EPR service. A local Bell
preparation acting on one half owned by each of two ranks would violate
the language's `pairwise_private` condition. Treating `create_epr` as such a
local atom would therefore invalidate the ownership theorem.

The conservative formal interface gives the program all required Bell pairs
as fresh independent shared input resources, one pair for each finite
teleport hop. `create_epr` is modeled as consuming the next pair from this
ideal resource service. Pre-sharing these independent pairs does not alter
the data computation: unused resource pairs remain untouched, and every
event uses its assigned pair only once. This connection is an explicit
source/resource abstraction obligation. A theorem about the private-language
program alone is not a theorem about the implementation of QMPI's service.

Similarly, the mathematical phase gates use exact real parameters. The
isQ source computes `double` phase values; floating-point rounding and
physical gate error are outside the exact Fourier theorem. A certified
compiler translation from isQ syntax is also a separate obligation.

## Circuit proof

The existing ascending circuit applies H at logical index `a`, then phases
controlled by logical indices `b > a`, and finally applies `S`. Its theorem
`ClassicalFourier.fourier_circuit_correct` identifies this circuit with `F`.
Write its prefix before the final reversal as `C`, so `S C = F`.

Conjugation by `S` maps index `a` to `n-1-a`. It maps an ascending target
layer to the corresponding descending physical layer, and preserves the
distance between target and control. Therefore the source circuit is
`S C S`. Since `S^2 = I`, the identity `S C = F` gives `D = F S`.
This is a mathematical explanation of the reversal convention. The
mechanized descending-circuit proof in `qft_model.v`
(`DistributedFourierAlgebra`) instead uses the
basis-state stage invariant below, while allowing arbitrary permutations
of the controls within one target layer.

After target `k` completes, its factor is

    (|0> + exp(2 pi i (b[k]/2 + b[k-1]/4 + ... + b[0]/2^(k+1))) |1>) / sqrt(2).

Higher target indices already have their final factors; smaller indices
still hold their original computational basis bits. The Hadamard creates
the first term of the phase, and each lower controlled phase adds exactly
one remaining term. Linearity extends the final basis equation to arbitrary
vectors and conjugation extends it to arbitrary density operators, including
states entangled with an external register.

## Distributed proof organization

The readable program in `DistributedQFTProgram` comes before these proofs
in `qft.v`. Its direct source loops and native process are connected by
`qft_rank_scriptE`, `qft_processE`, and `qft_programE` to the proof-side
instance described below. `qft_initializeE` and `qft_mainE` identify its
visible main/resource prefix. `DistributedQFTProgramCorrectness` applies
the resulting physical correctness and totality facts directly to
`qft_program` and `qft_main`. The connection uses structural equalities,
rather than a Fourier-correctness premise supplied by the caller.

`DistributedQFTSchedule` in `qft_model.v` records the layout, physical indices,
corrected cross-node distance, valid source layouts, and descending/return route. Its finite route
is lowered to the two correction-bit rendezvous for each teleport hop.
Local H and phase statements, Bell measurements, Pauli corrections, and
destination SWAPs are attached to the appropriate process initialization
or communication body.

`DistributedFiniteTrace` in `qft_model.v` provides a reusable local finite-trace
process. Every rank has a private integer program counter. Its branches are exactly its local
incident communications, guarded by equality with the counter, and each
body advances the counter after its local statements. Branch counts use
local projections: a false guard does not hide a channel from the
`point_to_point` ownership check. The helper proves well-formedness, finite
reads, classical ownership, quantum-region bounds, enabledness, final
termination, and the corresponding pure route projection facts.

Its message compiler packages the actual matching communications and local
endpoint bodies in `message_event`, projects them into `message_processes`,
and constructs the true rendezvous index in `message_index`. The theorem
`message_index_command` identifies its exact guard and command.
`message_command_progress` and `message_initial_boundary` prove control
progress for every nonzero kernel branch, including branches arising from
measurements. They require only distinct counter names and the syntactic fact
that payload operations do not write those counters.

After a completed global prefix, each endpoint's counter equals the number
of incident events in that prefix. The next global event appears at exactly
that local counter in both endpoint projections, so it is ready at both
ends. Every rendezvous increases two counters, and all counters are bounded
by their local trace lengths. This yields a finite legal schedule and excludes
premature deadlock along that schedule.

The source permits independent events to overlap at origin boundaries.
For example, rank `h-1` can start its own first qubit after forwarding the
last origin-`h` qubit, while rank zero is still returning that old qubit.
The serializer's lexicographic rendezvous order need not equal the displayed
global trace. Its semantics must be connected through the existing
confluence and scheduler-independence results, or through an explicit
serialization argument that commutes independent local events. Assuming
a unique enabled global event would be false. The existing theorem
`DistributedAllRendezvous.enabled_tail_kernel` already unfolds the actual
network semantics at any enabled rendezvous, using operational residual
semantics and scheduler independence. This permits induction on the intended
global route even when the serializer chooses a different independent event.

`message_source_tail_denote` uses that theorem, the concrete counter updates,
and final termination to identify the actual source tail with the ordered
message kernels. `message_source_program_denote` includes the real process
initializations. `message_source_program_run` extends the equality to
arbitrary cq inputs. Their hypotheses concern process syntax, private counter
names, and write footprints; they do not assume any Fourier or teleport
correctness result. `DistributedQFTInstance` in `qft_model.v` instantiates them
with the QFT's concrete register allocation and lowered teleport messages, including private namespaces,
disjoint quantum regions, matching channels, and actual counter updates.
`route_command_finishes` and `natural_route_tail_finishes` also state that
every nonzero final branch satisfies the network's termination predicate.
Successful termination with probability one additionally requires the
losslessness of the event kernels on the stated fresh-resource input.

The action-stream interface keeps the local source code explicit. A stream
contains a ranked local statement or a matching two-party message.
`project_actions` gives each rank exactly its own statement/communication
script. `segment_script` places the first local segment in initialization
and each later segment in the body of its preceding communication.
`assemble_actions_projection` proves that assembling those segments globally
has exactly the same local projections. Structural properties of individual
actions pass to the processes through `project_actions_preserves` and the
well-formedness, finite-read, ownership, quantum-region, and channel wrappers.
`assemble_actions_counter_fresh` also preserves freshness of every private
counter through the assembly. `action_source_program_denote` and
`action_source_program_run` then connect the actual projected distributed
program to its finite assembled-message command. Assembly can place an
independent local action earlier than the displayed global action stream;
`DistributedQFTExchange` in `qft.v` supplies the concrete gate, measurement,
store-update, and teleport-payload commutations for this source.

For that comparison, `linearize_command_denote` flattens sequential command
syntax while preserving its complete cq kernel. The generic
`command_interchange_denote` checks a finite rearrangement of pure command
labels and uses a proof that every permitted adjacent pair of interpreted
commands commutes. This comparison retains both measurement variables and
private program counters. A concrete instantiation must establish the two
label interpretations and discharge those local commutation facts using
classical ownership and disjoint quantum supports. `DistributedQFTExchange`
in `qft.v` performs this instantiation for the physical source, including the local counts that
determine each counter assignment.

`DistributedQFTCommutation` in `qft.v` supplies the physical primitive family
used for this step: constant local unitary, computational measurement, conditional local
correction, constant assignment, and copy assignment. Each has an exact
finite point-kernel representation. `finite_commands_commute` exchanges two
such kernels using commuting store updates, preservation of branch operators
under the other update, and commutation of those operators.
`independent_primitives_commute` derives those facts from disjoint classical
read footprints and disjoint quantum supports. In the QFT instantiation,
counter commands use the integer sort and payload bits use the Boolean sort;
other permitted exchanges act at disjoint endpoint ranks. The finite
`DistributedQFTInterleaving` certificate in `qft_model.v` records these permitted
source interchanges for all four accepted layouts of the literal eight-qubit main.

The checked theorem `source_action_canonical_denote` identifies the actual
assembled source command with its canonical payload followed by its counter
assignments. `source_program_canonical_run` lifts this result to the actual
distributed program on arbitrary cq inputs. Both finite interchange certificates
are interpreted as equalities of complete native cq kernels, including
measurement and copy assignments. These results do not assume the eventual
Fourier-channel equation.

`DistributedQFTCanonical` in `qft.v` groups the canonical payload into literal
local-gate and teleport-call commands and separates the deterministic counter tail. Its
`source_program_instruction_denote` is the denotational bridge needed by the
full physical proof; `source_counter_tail_execution` states the actual final
store update and identity quantum action. These canonical source helpers and
their composition with the physical data-channel theorem have passed native
checking in the `coqq` switch.

The concrete source instance uses `physical_memory`, a hardware-allocation
interface containing only native well-formed registers, disjoint data and
Bell-half registers, endpoint region inclusion, and disjoint process regions.
It does not contain a correctness equation. The baseline memory context is
finite, so an instance requires enough distinct physical labels for these
registers. Only transfer-step Bell pairs are prepared and consumed; the
uniform step-indexed register family also reserves unused slots for local
gate steps, which are auxiliary allocation slots rather than EPR resources.

The modules in `qft_teleport.v` extend the existing branch equation with frame,
correction, SWAP, and composition facts required by those relocations. The
literal native transfer kernel in `DistributedQFTTransferKernel` (`qft.v`)
sends x before measuring z and applies X, Z, and the destination SWAP in
source order. Its finite row equation
keeps the actual final classical stores, including overwrites of reused bit
variables. `DistributedQFTResources` in `qft.v` establishes the required
Bell-projector support using the explicit resource initializer and preserves the support of unused
pairs through each source branch.

`DistributedQFTStepSemantics` in `qft.v` follows the actual data carrier before
and after each native source instruction. Local H and phase branches induce the corresponding
logical gates. Each supported teleport branch induces the identity logical
gate with weight 1/4 on the relocated data register. The old destination slot
can have an arbitrary correlated state. `DistributedQFTComposition` in `qft.v`
sums the finite measurement histories while retaining their actual store
updates and combines these branch equations. `DistributedFourierAlgebra`
in `qft_model.v` identifies the complete descending logical circuit with `F S`.

The final connection is in `DistributedQFTCorrectness` (`qft.v`). Its
`source_program_channel` is the sum of the final-store rows of
`successful_sequentialize(processes(source_program))`, so the theorem concerns
the ownership-certified native distributed program. The canonical source
equality removes only the deterministic counter tail when forming this
quantum channel. `source_program_correct` proves

    reduced_data(source_program_channel(s)(rho))
      = D reduced_data(rho) D*,  where D = F composed with S.

Its only state premise is fresh Bell-projector support for the transfer-step
resources. `source_prepared_program_correct` discharges that premise with the
explicit native Bell preparation, which leaves the input data marginal
unchanged. The resulting data-channel equation applies to arbitrary operators
and every initial classical store, and retains all correlations among the
eight logical data qubits.

`source_initialized_program_correct` includes the literal main input
initializer and proves the output data operator is

    trace(rho) * |QFTbv(reverse main_input)><QFTbv(reverse main_input)|.

It has no state-correctness premise. `source_program_total` proves that the
successful executions have all of the input trace under the fresh-resource
contract. `source_initialized_program_total` proves the same equality after
the explicit main/resource initialization. For normalized positive input
states, these trace equations give successful termination with probability
one and exclude lost mass from blocked communication or nontermination in
the native semantics.

These four final theorems have passed native checking. Their physical source
scope is the literal `n=8` main and every accepted node count `{2,3,4,8}`,
with the hardware-allocation interface and exact fresh Bell resource service
described above. The mathematical Fourier and generic network helpers cover
their stated arbitrary sizes independently. The exact gate mathematics,
source-loop/layout certificates, native cq kernels, Bell resources, restored
data register, complete Fourier circuit, and successful mass are connected
in the final program proofs. QMPI service implementation, floating-point
phase rounding, physical gate error, and certified isQ compiler translation
remain outside this model.

## Validation

On 2026-10-07, the annotated corrected source and its correspondence checker
passed against a fresh full `coqq` Dune build. The checker derives 296
operations from the actual source across 17 rank traces and Rocq checks both
the source-list and concrete native-script equalities for every case. The
endpoint, phase-helper, and main token contracts also pass. The new
`qft_main_global_index_bound` and `qft_main_input_local` assumption reports
are closed under the global context. Fresh checks of the primary native
and initialized-main Hoare theorems match their preceding signatures and
complete eight-foundation assumption reports. The checker rejects temporary
variants restoring the old rank-zero index (at the three-node, rank-zero
Rocq equality) or removing the allocation guard (at the main token contract).
See the
[current validation record](VALIDATION.md#current-corrected-source-correspondence-checkpoint)
for the command and counts.

Native checking has completed in the named `coqq` switch, using OCaml 5.2.0
and Rocq 9.1.1. The schedule, source, location, and interchange certificates
cover all four accepted eight-qubit layouts. The native Fourier algebra,
register reduction, Bell and teleport proofs, resource initialization,
source lowering and allocation, finite network semantics, primitive
commutation, concrete exchange, canonical instruction stream, finite-history
composition, and physical step semantics have compiled successfully.
`DistributedQFTCorrectness` has also compiled through the final Fourier-state
and successful-mass theorems listed above.

The QFT files contain no `Admitted`, `admit`, or proof-level `Abort` commands,
and no new `Axiom` or `Parameter` declarations. This source scan does not
replace the theorem-assumption audit:
the development uses the repository's existing mathematical and memory
foundations.

After the three-file consolidation, header cleanup throughout both example
folders, contiguous native source view, and total Hoare specifications and
proofs, the repository-wide Dune build completed successfully on 2026-10-06
with exit status zero. All 70 source files match their Dune build inputs and
have compiled `.vo` artifacts, including the complete native network triples,
initializer composition, and state corollaries. The earlier consolidation
retained all 25 original named modules and 1,146 named declarations. The four
original `DistributedQFTCorrectness.source_*` theorem signatures remain
unchanged. Reproduce the build with:

```bash
opam exec --switch=coqq -- dune build -j4
```

The final `Check` and `Print Assumptions` audit completed successfully for
17 results: the four original `DistributedQFTCorrectness.source_*` results,
the four supporting channel results in `DistributedQFTProgramSemantics`, the
four native network Hoare results in `DistributedQFTProgramCorrectness`,
`qft_initialize_prepared_correct`, `qft_initialized_main_correct`, and the
three state corollaries. The original four source theorem signatures and
complete assumption reports match the preceding audit, ignoring whitespace.
The public `qft_program_correct` and `qft_main_correct` now state total Hoare
formulas; their former channel calculations have the explicit supporting
names `qft_program_channel_correct` and `qft_main_channel_correct`.
All 17 results report exactly the same eight existing foundation symbols:

- `ClassicalDedekindReals.sig_not_dec`
- `ClassicalDedekindReals.sig_forall_dec`
- `boolp.propositional_extensionality`
- `boolp.functional_extensionality_dep`
- `FunctionalExtensionality.functional_extensionality_dep`
- `Epsilon.epsilon_statement`
- `boolp.constructive_indefinite_description`
- `qreg.G`

These are the repository's existing classical/real foundations and finite
quantum-memory context. No additional QFT-correctness axiom appears in any
of the 17 theorem assumption reports.

The audit can be reproduced after the build with:

```coq
From quantum.example.distributive Require Import qft.
Print Assumptions DistributedQFTCorrectness.source_program_correct.
Print Assumptions DistributedQFTCorrectness.source_initialized_program_correct.
Print Assumptions DistributedQFTCorrectness.source_program_total.
Print Assumptions DistributedQFTCorrectness.source_initialized_program_total.
Print Assumptions DistributedQFTProgramSemantics.qft_program_channel_correct.
Print Assumptions DistributedQFTProgramSemantics.qft_program_channel_total.
Print Assumptions DistributedQFTProgramSemantics.qft_main_channel_correct.
Print Assumptions DistributedQFTProgramSemantics.qft_main_channel_total.
Print Assumptions DistributedQFTProgramCorrectness.qft_program_correct.
Print Assumptions DistributedQFTProgramCorrectness.qft_program_total.
Print Assumptions DistributedQFTProgramCorrectness.qft_main_correct.
Print Assumptions DistributedQFTProgramCorrectness.qft_main_total.
Print Assumptions DistributedQFTInitializationHoare.qft_initialize_prepared_correct.
Print Assumptions DistributedQFTProgramCorrectness.qft_initialized_main_correct.
Print Assumptions DistributedQFTProgramCorrectness.qft_program_state_correct.
Print Assumptions DistributedQFTProgramCorrectness.qft_initialized_main_state_correct.
Print Assumptions DistributedQFTProgramCorrectness.qft_initialized_main_physical_state_correct.
```
