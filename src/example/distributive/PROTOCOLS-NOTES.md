# Distributed protocol case studies

Source: distributive.pdf, Examples 2.1/2.3 and Section 6, PDF pp. 6–8 and
23–26. These notes describe the intended proofs; a claim is checked only when
its Rocq theorem name is explicitly identified below.

## Teleportation, Equation (7)

Alice owns q,q1; Bob owns q2. Initially q is an arbitrary normalized state psi
and q1,q2 share (|00>+|11>)/sqrt(2). Alice applies CNOT(q,q1), H(q), and measures
q and q1, recording zA and xA. The two stage-guarded rendezvous copy xA to xB
and then zA to zB. Bob applies X^xB followed by Z^zB. For each measurement
outcome z,x, the unnormalized branch vector after correction is

    (1/2) |z,x>_(q,q1) tensor psi_(q2).

To prove this without assumptions about the desired protocol result, expand
psi in the two computational basis vectors, expand the Bell pair, and evaluate
CNOT, H, the two projectors, and the Pauli corrections. Linearity extends the
four basis computations to arbitrary psi. Each branch has squared norm 1/4;
there are four branches and their sum is a trace-preserving channel. The
postcondition projects only Bob's register onto psi, so it holds with total
probability one. The stage guards allow exactly two communications and then
all processes terminate.

`DistributedProtocolExecution.teleport_rendezvousE` identifies the actual
serialized rendezvous list, and `teleport_loop_execution` certifies its two
iterations in the unbounded While semantics. The common theorem
`two_round_loop_execution` checks both guard choices and the final false
guard. `DistributedProtocolSuffix.teleport_loop_suffix_execution` additionally
checks the paper's final successful-termination test.

The source definitions and exclusivity/finite-read lemmas are checked in
`DistributedProtocolProcesses`. The exact operator equation is
`DistributedProtocolQuantum.teleport_branch_correct`.
`DistributedProtocolState.teleport_resource_isolf` and
`teleport_embed_isolf` prove normalization by preserving all computational
basis inner products: distinct input basis states remain orthogonal and each
Bell resource vector has two orthogonal summands of squared coefficient 1/2.
`DistributedProtocolState.teleport_channel_correct` proves the exact
one-quarter density-channel equation, including off-diagonal input terms.
`DistributedProtocolRegister.teleport_physical_branchE` connects the lifted
physical registers to that operator, and
`DistributedProtocolPre.teleport_serial_pre` computes the actual source
wp/wlp as the sum of its four branch duals.
`DistributedProtocolLocal.teleport_local_success` proves expectation one
against Bob's input-state projector.
The complete source-serialization result is
`DistributedTeleportCorrectness.teleport_correct` in
`teleport_correctness.v`, for both total and partial derivations. Its command
is the actual `successful_sequentialize` of the two concrete processes,
including both communications, the unbounded loop, and the termination test.
`teleport_preE` and `teleport_pre_inequality` are the connecting equalities
and projector inequality. The operational transfer described below now
connects this derivation to the actual distributed program.

## Remote CNOT, Equation (8)

Alice owns q,q1; Bob owns q2,r. The initial data state is an arbitrary normalized
psi on q,r, with a shared Bell pair on q1,q2. Alice applies CNOT(q,q1) and
measures q1 to xA. Bob applies CNOT(q2,r), H(q2), and measures q2 to zB.
The first rendezvous copies xA to xB and Bob applies X^xB on r. The second
copies zB to zA and Alice applies Z^zA on q. For each x,z, the unnormalized
corrected branch has data state CNOT psi and ancilla values q1=x,q2=z, with
amplitude (-1)^(x z)/2. This branch-dependent global sign cancels in the
density operator.

Expand psi in |i,j>, expand the Bell pair, and evaluate the same primitive
basis identities. The resulting data basis vector is |i,i xor j>, with the
remaining global sign (-1)^(x z), and all unwanted
bit flips canceled by Bob's X correction. Thus every outcome satisfies the
CNOT-output projector; all four branches together have probability one.
This argument proves the paper's target Equation (8) directly and does not
use its false intermediate invariant D6. The input vector psi and output
vector CNOT psi remain distinct throughout.

`DistributedProtocolExecution.remote_rendezvousE` and
`DistributedProtocolSuffix.remote_loop_execution` identify and execute the
two rendezvous; `remote_loop_suffix_execution` checks the final termination
test. Both stage variables become 2, so neither the stage-0 nor stage-1
guard remains enabled.

The checked operator equation is
`DistributedProtocolQuantum.remote_branch_correct`.
`DistributedProtocolState.remote_resource_isolf` and `remote_embed_isolf`
use the same computational-basis inner-product calculation. No restriction
to product data inputs occurs: linearity covers arbitrary entangled inputs
on q,r.
`DistributedProtocolState.remote_channel_correct` proves the corresponding
one-quarter density-channel equation. The scalar identity
`formso (a A) = (a conjugate(a)) formso A` removes the branch sign.
`DistributedProtocolRegister.remote_physical_branchE` checks the physical
register composition in the source program's exact order.
`DistributedProtocolRemoteLocal.remote_embed_adjoint` proves that distinct
ancillary outcome embeddings have orthogonal ranges. Consequently the four
vectors obtained by embedding CNOT psi are orthonormal, and their projector
sum is an effect (`remote_output_obs`): it is exactly the CNOT-output
projector on the data registers with the ancillary registers unrestricted.
`remote_output_embed` fixes each corrected output branch, and
`remote_local_success` proves total expectation one.
`DistributedProtocolRemotePre.remote_serial_pre` computes the actual remote
source wp/wlp as the sum of these four physical branch duals.
`DistributedProtocolRemoteOutput.remote_output_on_data` explicitly verifies
the postcondition operator on every ancillary sector: its composition with
`remote_embed x z` equals that embedding composed with the data projector
`|CNOT psi><CNOT psi|`.
`DistributedRemoteCorrectness.remote_correct` in `remote_correctness.v`
proves both total and partial derivations for the actual successful source
serialization. The operational transfer below also applies to this theorem.

## From probability one to an effect inequality

For any effect A and unit vector v, an expectation `<v,A v>=1` implies
`|v><v| <= A`. Indeed I-A is positive and has zero quadratic form on v;
the existing spectral positivity lemma implies `(I-A)v=0`, hence Av=v.
Writing P=|v><v| gives AP=PA=P and P²=P. Therefore
`A-P=(I-P)A(I-P)` is positive. This argument applies to the actual weakest
precondition effect, so branch probability one supplies the paper's projector
Hoare precondition without assuming protocol correctness.
This is checked as `DistributedProtocolEffect.effect_saturated` and
`effect_contains_state`.

The same reasoning works for a projector P of any rank, including a local
pure-state predicate tensored with the identity on all unused registers.
If PAP=P, then the quadratic form of I-A vanishes on every vector Pv, hence
(I-A)P=0. Thus AP=PA=P and again A-P=(I-P)A(I-P) is positive. This avoids
any assumption that the protocol registers exhaust the global quantum memory.
Alternatively, CoqQ's `liftf_lf_obsE`, `tf2f_lef`, and `liftf_lf_lef`
reflect the effect bounds and order of local predicates, allowing the
rank-one argument to be performed before lifting to the whole memory.

For the final source-program triple, first use the measured serialization's
wp/wlp branch sum and the physical-register branch equality. The resulting
global weakest precondition is the lift of a local operator A. Since wp/wlp
already returns an effect, `DistributedProtocolPredicate.register_predicate_obsE`
reflects its effect bounds to A. The local success calculation gives
`<resource psi,A(resource psi)>=1`; the resource isometry supplies unit norm.
`effect_contains_state` proves the local input-projector inequality, and
`register_predicate_le` lifts it to all global cq inputs, including arbitrary
states of unused registers. The checked completeness theorem of the explicit
classical inference system then produces its actual total/partial derivation.

## Source well-formedness and ownership

The programs use classical names (Alice,x), (Alice,z), (Alice,stage) and
(Bob,x), (Bob,z), (Bob,stage). Each expression has a finite set of reads; each
process reads and writes only its own three names. Distinct process-name
prefixes therefore establish classical privacy. The two stage guards compare
the same integer variable to 0 and 1 and cannot both hold. Every conditional
uses complementary Boolean guards, so it is exclusive as required by the
source language. Alice's quantum statements act only on her given register
or its projections, and likewise for Bob. Register validity bounds the
projections' footprints by their parent register, so disjoint parent registers
establish quantum privacy. With two processes there are no three distinct
owners, so point-to-point channel ownership is automatic. These are source
properties, proved separately from any desired protocol correctness claim.

`DistributedProtocolOwnership.teleport_program` and `remote_program` are now
checked source `program` values. Their only quantum-ownership parameter is
disjointness of the two supplied parent register footprints. The construction
proves classical privacy, quantum footprint bounds, finite reads, guard
exclusivity, nonempty process count, and point-to-point channels.

`DistributedOwnedProtocolCorrectness.teleport_network` and `remote_network`
instantiate those ownership proofs with the two projections of a valid joint
register. Their `_network_correct` theorems transport the checked total and
partial source-serialization derivations to the full source `program` values;
the serialized commands agree definitionally with the commands used in the
quantum calculation.

The final assumption audit of `teleport_correct`, `remote_correct`, and
`remote_output_on_data` reports only the inherited classical real-model,
choice and extensionality foundations, plus the existing `qreg.G` memory
parameter for the two program theorems. It reports no additional protocol
axioms, admitted results, or dependent-equality axioms.

## Transfer to distributed operational correctness

The scheduler-independent distributed denotation equals the denotation of
the successful serialization on every normalized point input
(`DistributedCorrespondence.denote_program_sequentialize`). The cq-input
mixture construction extends that equality to arbitrary subnormalized cq
states, using their countable component support and trace-weighted normalized
components. Consequently `DistributedHoare.valid_translate_iff` equates the
actual distributed expectation inequalities with the checked classical
judgment for the serialization. Applying classical derivation soundness and
this equivalence to the owned protocol wrappers proves
`DistributedProtocolCorrectness.teleport_correct` and `remote_correct` in
`protocol_distributed_correctness.v`, for both total and partial correctness.
Their semantics is the original interleaving/rendezvous semantics with
unbounded successful-state limits.
The mapped assumption audit of both operational protocol theorems reports
the same inherited foundations and `qreg.G` as the serialization proofs.

The protocol operational triples also yield independent network-rule
derivations through the checked operational completeness theorem.
`DistributedProtocolDerivations.teleport_derive` and `.remote_derive` cover
both correctness modes; their premises are exactly the physical register
and normalized input conditions of the source protocol theorems.
