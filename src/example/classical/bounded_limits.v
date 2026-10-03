(* Order separation and continuous expectations. See EXPECTATION-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import state kernel language kernel_limits bounded_unroll.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module ClassicalBoundedLimits.
Import ClassicalLanguage ClassicalBoundedUnroll.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation row := ({summable cmem -> 'SO(Hq)}).
Definition kernel_chain (f : nat -> kernel) :=
  forall s, nondecreasing_seq (fun k => f k s).

Lemma sem_limit_cvg f : kernel_chain f -> forall s,
  (f k s : row) @[k --> \oo] --> (sem_lim f s : row).
Proof.
move=>inc s.
have C := vdnondecreasing_is_cvgn (@choinorm_ge0_add Hq Hq) (inc s).
change ((fun k => (f k s : row)) @ \oo -->
  ((vdlim (FF := eventually_filter) (fun k => f k s)) : row)).
by rewrite vdlimE.
Qed.
Lemma sem_limit_upper f : kernel_chain f -> forall k, kernel_le (f k) (sem_lim f).
Proof.
move=>inc k s.
exact: (vdnondecreasing_cvg_le (@choinorm_ge0_add Hq Hq) (inc s) k).
Qed.
Lemma sem_limit_least f K : kernel_chain f ->
  (forall k, kernel_le (f k) K) -> kernel_le (sem_lim f) K.
Proof.
move=>inc ub s; rewrite levdEsub.
have C := @sem_limit_cvg f inc s.
have L : limn (fun k => (f k s : row)) ⊑ (K s : row).
  apply: lim_les_nearF; first exact: (cvgP _ C).
  apply: nearW=>k; by rewrite -levdEsub; apply: ub.
by rewrite (cvg_lim (@norm_hausdorff _ _) C) in L.
Qed.

Lemma if_limit b (f g : nat -> kernel) :
  sem_lim (fun k => if_sem b (f k) (g k)) = if_sem b (sem_lim f) (sem_lim g).
Proof.
apply/semtypeP=>s.
change (vdlim (FF := eventually_filter)
  (fun k => if esem b s then f k s else g k s) =
  if esem b s then vdlim (FF := eventually_filter) (fun k => f k s)
  else vdlim (FF := eventually_filter) (fun k => g k s)).
by case: (esem b s).
Qed.
Lemma iter_chain b f : kernel_chain f -> forall r,
  kernel_chain (fun k => while_sem_iter b (f k) r).
Proof.
move=>inc r s j k jk; apply: iter_mono_body=>t; exact: inc t j k jk.
Qed.
Lemma iter_limit b f : kernel_chain f -> forall r,
  sem_lim (fun k => while_sem_iter b (f k) r) = while_sem_iter b (sem_lim f) r.
Proof.
move=>inc; elim=>[|r IH]; first exact: sem_lim_cst.
change (sem_lim (fun k => if_sem b (slet (f k) (while_sem_iter b (f k) r)) skip_sem) =
  if_sem b (slet (sem_lim f) (while_sem_iter b (sem_lim f) r)) skip_sem).
by rewrite if_limit sem_lim_cst (slet_lim inc (@iter_chain b f inc r)) IH.
Qed.
Lemma diagonal_chain b f : kernel_chain f ->
  kernel_chain (fun k => while_sem_iter b (f k) k).
Proof.
move=>inc s j k jk.
apply: (le_trans (@iter_mono_body b _ _ (fun t => inc t j k jk) j s)).
exact: while_sem_iter_homo jk.
Qed.

Lemma while_diagonal_limit b f : kernel_chain f ->
  sem_lim (fun k => while_sem_iter b (f k) k) = while_sem b (sem_lim f).
Proof.
move=>inc; apply: kernel_le_anti.
- apply: sem_limit_least; first exact: diagonal_chain inc.
  move=>k s; apply: (le_trans (@iter_mono_body b _ _ (sem_limit_upper inc k) k s)).
  exact: while_sem_ub.
- move=>s; apply: while_sem_least=>r.
  rewrite -(@iter_limit b f inc r).
  apply: sem_limit_least; first exact: (@iter_chain b f inc r).
  move=>k t.
  apply: (le_trans (y := while_sem_iter b (f (maxn k r)) (maxn k r) t)).
  + apply: (le_trans (@iter_mono_body b _ _ (fun u => inc u k (maxn k r) (leq_maxl k r)) r t)).
    exact: while_sem_iter_homo (leq_maxr k r).
  + exact: (@sem_limit_upper
      (fun j => while_sem_iter b (f j) j)
      (@diagonal_chain b f inc) (maxn k r) t).
Qed.

Theorem bounded_unroll_limit c :
  sem_lim (fun k => denote (bounded_unroll k c)) = denote c.
Proof.
elim: c=>[| |u x e|u x prob|u v x q M|u q phi|u q U|
  c IH d IHd|b c IH d IHd|b c IH].
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- change (sem_lim (fun k => slet (denote (bounded_unroll k c)) (denote (bounded_unroll k d))) =
    slet (denote c) (denote d)).
  by rewrite (slet_lim (bounded_unroll_chain c) (bounded_unroll_chain d)) IH IHd.
- change (sem_lim (fun k => if_sem b (denote (bounded_unroll k c)) (denote (bounded_unroll k d))) =
    if_sem b (denote c) (denote d)).
  by rewrite if_limit IH IHd.
- have E : (fun k => denote (bounded_unroll k (While b c))) =
      (fun k => while_sem_iter b (denote (bounded_unroll k c)) k).
    by apply/funext=>k; rewrite /= denote_unroll.
  by rewrite E (while_diagonal_limit b (bounded_unroll_chain c)) IH.
Qed.

Theorem bounded_unroll_cvg c s :
  (denote (bounded_unroll k c) s : row) @[k --> \oo] --> (denote c s : row).
Proof.
have C := @sem_limit_cvg (fun k => denote (bounded_unroll k c))
  (bounded_unroll_chain c) s.
by rewrite bounded_unroll_limit in C.
Qed.
Theorem bounded_unroll_suffix_limit c (K : kernel) :
  sem_lim (fun k => slet (denote (bounded_unroll k c)) K) = slet (denote c) K.
Proof. by rewrite (slet_liml K (bounded_unroll_chain c)) bounded_unroll_limit. Qed.

End ClassicalBoundedLimits.
