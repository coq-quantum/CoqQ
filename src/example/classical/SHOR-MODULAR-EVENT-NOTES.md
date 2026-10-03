# Reduction of the distinguished modular involution

This supplies the concrete involution compatibility needed by the order-event
argument for classical.pdf Lemma 7.2(2), PDF pp. 40–41. Let M divide N and
assume M,N>1. The unit called `negative_one N` has canonical representative
N−1. The canonical unit reduction sends it to the representative
(N−1) mod M. Since N is divisible by M and positive, the predecessor
remainder formula gives (N−1) mod M=M−1. This is exactly the representative
of `negative_one M`. Injectivity of canonical unit representatives proves
the equality of the actual group elements. No order-finding correctness or
extra arithmetic hypothesis is used.

The checked results in `shor_modular_event.v` are
`ClassicalShorModularEvent.predecessor_mod_divisor` and
`ClassicalShorModularEvent.unit_reduce_negative_one`. They use the canonical
reduction from `ClassicalShorCRT` and concrete `negative_one` from
`ClassicalShorPrimePower`.
