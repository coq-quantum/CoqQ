# CoqQ reference and attribution

The implementation follows the classical/quantum kernel already present in
`../veri_QEC/cqwhile.v` and consults the Coq Quantum Development Team's
[CoqQ development](https://github.com/coq-quantum/CoqQ).

The upstream reference was checked on 2026-10-03 against commit
`b169ea462b13d20b05e03615ad1d56cc8d8f5784` (commit date 2024-12-28,
message `v1.2`). GitHub's commit and recursive tree APIs were retrieved, and
the Git blob hashes of the local reference copies matched that pinned tree:

| Reference file | Git blob |
| --- | --- |
| [`qwhile.v`](https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/src/example/coqq_paper/qwhile.v) | `c61a0a0e161e64278a2c4ba59aee4163e2a00923` |
| [`qhl.v`](https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/src/example/coqq_paper/qhl.v) | `020a47726b5314626dcd302ef5207c8448f176e9` |
| [`example.v`](https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/src/example/coqq_paper/example.v) | `5f5441508ddcea51368267073cc77081e75d9fea` |

The pinned upstream root `LICENSE` is the MIT License, copyright CoqQ
contributors (see AUTHORS); its exact text is retained in
[`UPSTREAM-LICENSE`](UPSTREAM-LICENSE). Its blob is
`ed5b4192bfd216977029c75f4ebfd04a81b62109`. The local package manifest instead
declares `CeCILL-B`; this note preserves the upstream notice and does not
change or resolve the licensing of the rest of this workspace. No upstream
copyright or permission notices have been removed.

## Relevant proof patterns

* `qwhile.v:global_hoare` quantifies over partial density operators. Its
  total interpretation is `Tr(P rho) <= Tr(Q (sem c rho))`; the partial
  interpretation adds the lost trace, as proved by `partial_alter_G`.
* `qhl.v:Ax_Sk_G`, `Ax_In_G`, `Ax_UT_G`, `R_IF_G`, `R_SC_G`, and `R_Or_G`
  prove primitive and structural rules by unfolding semantics, using trace
  duality, and chaining inequalities.
* `R_LP_GP` proves the partial loop rule first for finite unfoldings and
  then takes a justified limit. `R_LP_GT` additionally uses a ranking
  function; termination is not inferred from the invariant alone.
* `wp` and `wlp` are dual-superoperator constructions; `wp_LP1` and
  `wlp_LP` derive fixed-point equations from `while_fsem_fp`.
* `example.v:R_HHL_loop_P` and `R_HHL_P` demonstrate modular use of loop,
  sequence, initialization, and consequence rules, with operator arithmetic
  proved separately.

Upstream's `global_hoare` is semantic validity and its rules are sound
lemmas about that validity. To formalize a paper's derivability relation,
the new development must additionally use an independently defined
inference system and prove its soundness; simply renaming
`global_hoare` as derivability would not formalize that system.

## Reused local APIs

`cqwhile.v` already provides unrestricted classical memories, typed
expressions, `cmd_`, superoperator-valued kernels `semType`, composition
`slet`, and unbounded while semantics `while_sem`. Its structural results
include `sletA`, `slet1l`, `slet1r`, `slet_lim`, `while_sem_iter_homo`,
`while_sem_is_cvg`, `while_sem_ub`, `while_sem_least`, and
`while_sem_fixpoint`. Its operational relation `trans_rule` and route
enumeration culminate in `equal_OS_DS`.

`summable.v` already proves `summable_countn0` for arbitrary index
`choiceType`s. `VDistr` supplies positivity, summability, norm mass bounds,
and convergent increasing limits. `quantum.v` supplies positive operators
and effects (`'F+`, `'FO`), `lef_psdtr`, `trlfM_ge0`, and
`psd_trfnorm`; thus no parallel finite-support state model or separate
matrix-trace theory is needed.
