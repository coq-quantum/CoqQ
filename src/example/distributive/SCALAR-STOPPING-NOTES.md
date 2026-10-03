# Local stopping for a bounded nonnegative scalar potential

For total network completeness, the potential is the remaining expectation
of the target postcondition after subtracting a finite operational horizon.
A fixed such potential lies in [0,1] and is superharmonic for every legal
one-step transition. We need its inequality after a complete local body,
which may itself have unbounded loops.

Assume a potential V is nonnegative and has absolute value at most one on
the serial invariant, and that the expected V of every actual global-step
successor family is at most its value before the step. Assume the completed
local endpoint bounds the expectation of assertion A. For depth N, induction
bounds the wp expectation of `local_iter N s` by V at the lifted local
configuration. At depth zero an unfinished command contributes zero, bounded
by nonnegativity; an already finished command uses the endpoint bound. At a
successor depth, the exact local-unfold wp formula writes this expectation
as a probability-weighted sum of continuation expectations. The identity
`weight * normalized_output = operation(input)` proves this formula even
for zero-probability outcomes. Actual global local-step closure preserves
the serial invariant at every branch. Apply the induction hypothesis to
successful-store branches and nonnegativity to failed-store branches, then
apply the one-step superharmonic inequality.

Countable random-assignment supports cause no finite-support restriction:
all continuation wp pairings and all reachable potential values have norm
at most one, so multiplying by the probability family gives absolutely
summable scalar families. Termwise inequalities therefore pass to their
sums. Finally, completed-local iterations converge to the entire translated
local denotation. Continuity of wp pairing passes the finite inequalities
to the limit. This is a bounded stopping argument and needs neither a finite
iteration bound nor a finite expected running time.

For a finite list of distinct active processes, fold this local stopping
lemma over the list. If the head process is executing s, take the wp of the
remaining list and final tail as its local postcondition. Its completed
endpoint has that process's idle control, and the induction hypothesis
supplies the required bound there. The remaining commands are unchanged by
this control replacement because their indices are distinct. Waiting and
stopped head processes contribute skip and leave the control vector alone.
The final endpoint is `finish_controls` of the entire list. This gives the
scalar counterpart of the existing active-program lower-bound argument.

The checked finite theorem is
`DistributedScalarStopping.local_iter_stopping`. Its absolute-sum comparison
and normalized one-step identity are `observe_mono_branches` and
`local_unfold_observe`. `DistributedScalarStoppingLimit.translated_local_stopping`
passes to the full local command using
`DistributedLocalExpectationLimits.local_wp_pairing_least`.
`DistributedActiveStopping.active_program_stopping` folds the result over
distinct process indices with an arbitrary final tail;
`active_commands_stopping` specializes that tail to Skip.

The mapped audit of the finite and full local stopping theorems, including
the final `active_commands_stopping` theorem, reports only
the inherited classical foundations and existing `qreg.G` memory parameter.
The generic scalar-potential premises are explicit parameters; the total
network-ranking development proves them for its concrete horizon remainders.
