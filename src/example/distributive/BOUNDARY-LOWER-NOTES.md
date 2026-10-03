# Terminating boundaries in the operational value

The lower direction of the sequentialization theorem needs the loop-exit
case for every ready control vector, including vectors containing already
stopped processes. If TERM holds, every waiting process has all its guards
false. The operational process-done transition can therefore stop each
waiting process, in enumeration order, without changing the classical store
or quantum state. Already stopped processes need no transition. The finite
path constructed by `terminate_stop_list`, followed by `stop_enum`, reaches
the all-stopped configuration.

A deterministic global step from an owned normalized configuration preserves
ownership and normalization. Its projected step has a singleton successor
(possibly with failure collapsed). The Bellman equation for the successful
operational value equates the current value to that successor's value;
`value_collapse` removes the failure projection. Induction over a finite
path therefore preserves value. At the all-stopped configuration the terminal
value equals the successful component, which is exactly the identity kernel
on the unchanged classical store applied to the unchanged density operator.
This proves equality, and hence the required lower inequality, without a
scheduler fairness assumption or any bound on surrounding loop iterations.

Formal statements are in `boundary_lower.v`: `deterministic_step_value`,
`deterministic_steps_value`, `ready_term_value`, and `ready_term_lower`.
The mapped assumption audit of `ready_term_value` reports only inherited
classical foundations and the existing `qreg.G` memory parameter.
