# Arbitrary ambient memory in Change and Access

## Paper and missing step

`distributive.pdf`, page 11, Lemma 3.4(5), says that a transition can be
replayed in any quantum memory containing the program's quantum variables.
The existing `DistributedChangeAccess.descriptor_replay` establishes replay
only in the fixed ambient memory of the original `qreg.G`. The missing step
is an actual operational interpretation on a separately chosen tensor memory,
including memories that do not contain unused variables of `G`.

The model parameters are a source footprint `S`, a finite target label type
`L`, Hilbert spaces `H l`, sets `T ⊆ V` of target labels, and a unitary
identification `U : H_S → H_T`. The identification records how the program's
quantum variables are represented in the new memory. It is an explicit
interpretation parameter, not a hypothesis about the transition theorem.
Taking the usual corresponding variable spaces gives the paper's literal
memory extension. The input density operator has trace one, as required by
the paper's definition of a configuration on page 10. Zero-probability
branches remain represented in the indexed family but have no probabilistic
support; their stored normalized state is the input state.

## Mathematical argument before formalization

For a channel `E` acting on the footprint, let

`J(E) = lift_(T⊆V)(Ad_U ∘ E ∘ Ad_(U†))`.

Unitary conjugation and tensoring with the identity preserve complete
positivity, trace preservation, and trace nonincrease. They preserve the
identity, addition, and scalar multiplication. For every source register
`q ⊆ S`, interpret its initialization, unitary update, and measurement
directly: extend each register Kraus operator to `S`, conjugate it by `U`,
then extend it to `V`. The Kraus expansion shows that each interpreted
primitive equals `J` applied to its channel on `S`. This equality is a
theorem about those independently defined primitive operations.

Define target local and distributed transition relations by the rules of
Table 1. The classical operations, guard tests, rendezvous matching, residual
syntax, and scheduler choice are unchanged. Quantum premises require that
the register lies in `S` and use the directly interpreted primitive channels.
In particular, the target relation is not defined by transport of a source
transition or by the conclusion of the replay theorem.

Induction on the sequential instruction gives a canonical target branch
family. The branch index and residual classical control are the same as in
the source interpretation. Its operator is `J(E_i)`, where `E_i` is the
instruction's source branch map on `S`. For a channel branch, its trace is
one and normalization changes nothing. For a random-assignment branch,
the map is a nonnegative scalar multiple of the identity, so normalization
again returns the input state whenever its weight is positive. Measurement
uses the trace and normalized output of the interpreted branch directly.
Sequence adds the same continuation to every residual; guards choose the
same branch. These observations prove canonical realization from the actual
target transition rules, including zero-weight outcomes.

Now fix a source distributed step and its enabled descriptor. Ownership of
the residual instruction places its quantum footprint inside the network
footprint `S`. Agreement of stores on the network's read variables preserves
every guard, communication match, evaluated quantum expression, random
distribution, and relevant classical update. Hence the same descriptor is
enabled in the new store. Apply the independently proved target realization
theorem. The resulting family has the original residual controls, the
classical updates evaluated in the new store, and weights
`tr(J(E_i)(rho'))`; its positive-weight normalized states are
`J(E_i)(rho') / tr(J(E_i)(rho'))`. This is precisely the replay clause.

The original instrument, classical frame, and locality witnesses remain
those already supplied by `global_step_change_access`. The new theorem
extends the ambient-memory component without changing those witnesses.
More explicitly, define each source-footprint branch map from the instruction
syntax and prove that extending it to the original full memory gives the
existing branch map. The norm of a footprint map is bounded above by the norm
of its identity extension. Therefore summability of the existing instrument
implies summability of the footprint instrument. The finite-dimensional
linear extension commutes with the convergent sum. Complete positivity and
trace nonincrease are reflected by identity extension, so the footprint sum
is completely positive and trace-nonincreasing. This proves the source-space
instrument property for the very same maps used in every target memory.

The network wrapper uses the original processes' union of quantum footprints.
This can include registers occurring only in an initialization or a process
that has already stopped. It is consequently a source-process footprint
result. The instruction-level replay theorem accepts any containing `S`,
but this layer does not identify a minimal quantum-variable set for every
residual distributed configuration.

## Formalization and validation

`memory_replay.v`, module `DistributedMemoryReplay`, now proves:

- `local_step_probability`, `local_step_normalized`,
  `global_step_probability`, and `global_step_normalized` for the independent
  target Table 1 transition rules.
- `atom_realization`, `local_realization`, and `descriptor_step`, deriving
  canonical target successors from those rules.
- `source_local_mapE` and `source_local_map_cp`, identifying explicit
  completely positive branch maps on the source footprint.
- `source_local_maps_summable` and `source_local_maps_cptn`, establishing the
  countable source instrument and its trace-nonincreasing sum.
- `local_map_covariance` and `replay_family_transport`, identifying the
  target branch maps with the transport of exactly that source instrument.
- `descriptor_replay`, `global_step_memory_replay`, and
  `global_step_memory_change_access`, returning actual target transitions
  together with probability and normalization guarantees. The last theorem
  retains the original `change_access_witness`, including its classical
  frame, read agreement, original realization, and ownership properties.

The complete module passed direct Rocq compilation, qualified Dune
integration, and the mapped seven-result assumptions audit. The audit covers
local probability, global normalization, source summability, source summed
trace nonincrease, covariance, the transported replay family, and the final
`global_step_memory_change_access` theorem. Its only assumptions are the
inherited real/classical foundations and the existing `qreg.G` model
parameter. No new axiom or admission was introduced. An independent read-only
review also checked that the actual target semantics precedes the replay
proof and that the shared source maps support both memory interpretations.

Validation logs are
`/private/tmp/coqq-distributive-next/memory-replay/compile.log` and
`/private/tmp/coqq-distributive-next/memory-replay/audit.log`.
