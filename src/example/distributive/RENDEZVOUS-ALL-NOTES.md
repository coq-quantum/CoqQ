# Every enabled rendezvous preserves the network-tail value

The relative-completeness argument for the network rule needs an invariant
for every enabled rendezvous, including commands that occur after the first
one in the serialization's priority list. A syntactic while-unfolding equation
only establishes the first enabled case and does not justify the others.

Use the proved operational/serialized correspondence at residual
configurations instead. Begin with the idle control vector, normalized
quantum state, and the given store. Any enabled rendezvous gives an actual
deterministic communication transition: its typed assignment updates the
receiver's store, then the two communicating bodies become active. The
serial invariant is preserved by that transition. Bellman's equation gives
equality of operational values at its endpoints. Residual correspondence
turns this into equality of their serialized residual denotations. The source
residual is the network tail; the destination residual is the first body,
then the second body, then that same network tail. Combining the typed
assignment with the latter gives exactly the selected rendezvous command
followed by the network tail. This argument applies to every enabled index,
without a priority hypothesis.

Equality on normalized density matrices extends to positive operators by
multiplying by their trace (the zero-trace positive case is the zero
operator), and then to all operators by the existing positive-operator
separation theorem for superoperators. Thus the result is a kernel-row
equality and can be used for both weakest and weakest-liberal preconditions.

Checked theorem names in `rendezvous_all.v` are
`DistributedAllRendezvous.enabled_tail_normalized`, `enabled_tail_kernel`,
`enabled_tail_pre`, `enabled_tail_invariant`, and `all_tail_invariants`.
The final theorem gives the required invariant for the entire actual
`rendezvous_commands` list, in both total and partial correctness.
Its mapped assumption audit reports only inherited classical foundations
and the existing `qreg.G` memory parameter.
