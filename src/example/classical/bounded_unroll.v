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
From quantum.example.classical Require Import state kernel language kernel_limits.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module ClassicalBoundedUnroll.
Import ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.

Fixpoint bounded_unroll (k : nat) (c : command) : command :=
  match c with
  | Sequence a b => Sequence (bounded_unroll k a) (bounded_unroll k b)
  | Conditional b a d => Conditional b (bounded_unroll k a) (bounded_unroll k d)
  | While b a => unroll b (bounded_unroll k a) k
  | _ => c
  end.

Definition kernel_le (K L : kernel) := forall s, K s ⊑ L s.
Lemma kernel_le_refl K : kernel_le K K.
Proof. by move=>s. Qed.
Lemma kernel_le_trans K L M : kernel_le K L -> kernel_le L M -> kernel_le K M.
Proof. move=>KL LM s; exact: le_trans (KL s) (LM s). Qed.
Lemma kernel_le_anti K L : kernel_le K L -> kernel_le L K -> K = L.
Proof. move=>KL LK; apply/semtypeP=>s; apply: le_anti; by rewrite KL LK. Qed.
Lemma abort_le K : kernel_le abort_sem K.
Proof. move=>s; apply/levdP=>t; rewrite abort_semE; exact: vdistr_ge0. Qed.

Lemma slet_mono K K' L L' : kernel_le K K' -> kernel_le L L' ->
  kernel_le (slet K L) (slet K' L').
Proof.
move=>KK LL s; apply/levdP=>t; change (slet_def K L s t ⊑ slet_def K' L' s t).
rewrite /slet_def; apply: lev_lim.
- apply: norm_bounded_cvg; exact: slet_in_out_summable.
- apply: norm_bounded_cvg; exact: slet_in_out_summable.
- move=>A; apply: lev_sum=>i _; apply: leso_comp; try exact: vdistr_ge0.
  + by move: (LL (val i))=>/levdP/(_ t).
  + by move: (KK s)=>/levdP/(_ (val i)).
Qed.
Lemma if_mono b K K' L L' : kernel_le K K' -> kernel_le L L' ->
  kernel_le (if_sem b K L) (if_sem b K' L').
Proof. by move=>KK LL s; rewrite !if_semE; case: (esem b s); [exact: KK|exact: LL]. Qed.
Lemma iter_mono_body b K L : kernel_le K L -> forall k,
  kernel_le (while_sem_iter b K k) (while_sem_iter b L k).
Proof.
move=>KL; elim=>[|k IH]; first exact: kernel_le_refl.
apply: if_mono; last exact: kernel_le_refl.
exact: slet_mono KL IH.
Qed.
Lemma while_mono_body b K L : kernel_le K L ->
  kernel_le (while_sem b K) (while_sem b L).
Proof.
move=>KL s; apply: while_sem_least=>k.
apply: (le_trans _ (while_sem_ub b L k s)); exact: iter_mono_body KL k s.
Qed.

Lemma bounded_unroll_mono c : forall j k, (j <= k)%N ->
  kernel_le (denote (bounded_unroll j c)) (denote (bounded_unroll k c)).
Proof.
elim: c=>[| |u x e|u x prob|u v x q M|u q phi|u q U|
  c IH d IHd|b c IH d IHd|b c IH] j k jk.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: slet_mono (IH j k jk) (IHd j k jk).
- exact: if_mono (IH j k jk) (IHd j k jk).
- move=>s; rewrite /= !denote_unroll.
  apply: (le_trans (@iter_mono_body b _ _ (IH j k jk) j s)).
  exact: while_sem_iter_homo jk.
Qed.
Lemma bounded_unroll_upper c : forall k, kernel_le (denote (bounded_unroll k c)) (denote c).
Proof.
elim: c=>[| |u x e|u x prob|u v x q M|u q phi|u q U|
  c IH d IHd|b c IH d IHd|b c IH] k.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: slet_mono (IH k) (IHd k).
- exact: if_mono (IH k) (IHd k).
- move=>s; rewrite /= denote_unroll.
  apply: (le_trans (@iter_mono_body b _ _ (IH k) k s)); exact: while_sem_ub.
Qed.
Lemma bounded_unroll_chain c s : nondecreasing_seq (fun k => denote (bounded_unroll k c) s).
Proof. move=>j k jk; exact: bounded_unroll_mono jk s. Qed.

End ClassicalBoundedUnroll.
