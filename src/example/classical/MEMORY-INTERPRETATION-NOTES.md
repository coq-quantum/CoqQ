# Distinct finite-memory interpretation: construction and API

This construction addresses classical Section 4.2's domains and distributive
Lemma 3.4(5), whose ambient finite memory V can be any memory containing the
program's quantum footprint. It preserves the actual cqwhile source syntax,
including typed registers and state-dependent classical, measurement,
initialization and unitary expressions. It does not change qreg.G.

Fix an original subsystem S containing the command's quantum footprint.
Let L be any finite label type, H:L->chsType any target tensor system, T and
V target label sets with T contained in V, and U a packed global isometry
from H[msys]_S to H[H]_T. This is a basis/register interpretation, not a
correctness hypothesis. S may equal the program footprint; consequently V
need not contain the unused portion of the original qreg.G. A concrete
register-preserving identification of equal typed variables induces such U.
The theorem quantifies over all choices of finite target memory and U.

For a source register q with mset(q) contained in S, interpret a typed
operator A on q by first applying the existing tf2f q q A, lifting q to S,
conjugating by U, and lifting T to V. This preserves its type and all
state-dependent expression evaluations (the classical store is unchanged).
Interpret a unitary primitive by formso of this operator. Interpret each
measurement outcome by formso of its interpreted measurement operator.
Interpret initialization through its actual reset Kraus family
|tv2v(q,phi)><eb_i| on q: lift, conjugate and lift each Kraus operator, then
sum their form maps. These primitive definitions use the actual constructors
and do not define execution by a desired descriptor-replay equation.

The algebraic proof uses conjugation of superoperators:
conjugate_U(E) = formso(U) o E o formso(U^A).
Global-isometry cancellation proves preservation of identity, composition,
complete positivity, trace preservation and trace nonincrease. Kraus
expansion proves conjugate_U(krausso f) = krausso(U f_i U^A). Existing
liftso_krausso and liftso_formso identify each independently interpreted
primitive with liftso(T<=V)(conjugate_U(liftso(q<=S)(source primitive))).
This proves primitive covariance, including measurements and reset.

An interpreted classical small-step relation copies the source Table 2
constructors with the new primitive channels and target quantum state type.
Each constructor includes only the local footprint inclusion needed to
interpret its actual register. It retains the same assignments, random
outcomes, guards, sequencing and while unrolling. Structural induction on
source steps proves replay at every target input using the same branch
choices and residual/classical results, with quantum output determined by
the interpreted local branch map. The quantum output is not assumed to be
a direct transport of the old full-memory input: arbitrary new inputs may
have additional entanglement and different marginals.

For distributed source statements, define the analogous primitive/local
interpreter independently. Guard and communication control use the existing
classical expressions; primitive branch maps use the above construction.
Structural induction on the local/global transition rules gives replay in
the new memory. Prove normalization for normalized new density input; the
configuration definition requires trace one even though Lemma 3.4(5) writes
D(H_V). Subnormalized inputs belong to the separate linear cq-state
extension, not to a probability-one branch family.

The common formal APIs are `CQMemoryTransport.conjugate_formso` and
`conjugate_krausso` in `memory_transport.v`, and
`CQMemoryInterpretation.unitary_channelE`, `measurement_channelE`,
`initialize_channelE`, `measurement_sum_tp`, and `transport_original` in
`memory_interpretation.v`. `transport_summable` and `transport_sum` extend
the same construction to arbitrary summable branch families. The primitive
module, including all summation helpers, has passed direct and qualified
Dune compilation.

`ClassicalMemorySteps.memory_step` in `memory_steps.v` is the independently
defined classical Table 2 relation. Its `step_replay` constructs a footprint
operator and the replayed step for each target input; this is an informative
witness, not a correctness parameter. `source_step_quantum` tracks the
residual footprint. `memory_step_positive`, `memory_step_trace_le`, and
`memory_step_density` verify state preservation directly for this new
relation. The classical replay module has passed direct and qualified Dune compilation.
The corresponding distributed implementation is
`DistributedMemoryReplay` in `distributive/memory_replay.v`; its own note
records the checked global replay API.

The scope of this layer is primitive interpretation and one-step operational
replay across memory contexts. Cross-context denotational semantics for full
unbounded programs and transport of Hoare derivations are separate results;
they are not claimed here. No target replay/covariance property is a model
parameter.

Preservation of positive operators and density operators in the interpreted
small-step relation follows directly by induction on its constructors.
Random weights lie between zero and one; measurement branch maps are
completely positive and trace-nonincreasing; initialization and unitary
maps are channels. Structural constructors preserve those facts. The
identity interpretation (the same S, original target full memory, and
identity U) reduces transport to the original liftfso, providing the
original model as an instance of the new interpretation.


Mapped assumption audits of all primitive covariance theorems, measurement
normalization, summation transport, original-model recovery, classical step
replay, density preservation and residual support passed. They use only the
inherited classical-real/choice/extensionality foundations and the original
source-language memory parameter `qreg.G`; no new axioms or admissions were
introduced. The target memory and its footprint identification are explicit
theorem parameters, not additional global assumptions.
