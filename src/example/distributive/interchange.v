(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import footprint.
From quantum.example.distributive Require Import language operational scheduler local_actions instruments.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedInterchange.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma local_map_atom s m i a t j :
  [disjoint statement_quantum s & atom_quantum a] ->
  @local_map s m i :o @atom_map a t j = @atom_map a t j :o @local_map s m i.
Proof.
case: a j=>[| |u x e|u x p|u q phi|u q U|u v x q M] j /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- by rewrite comp_soZl comp_soZr comp_so1l comp_so1r.
- exact: local_map_external.
- exact: local_map_external.
- rewrite CL.measurement_branchE; exact: local_map_external.
Qed.

Lemma local_map_commute s t m1 m2 i j :
  [disjoint statement_quantum s & statement_quantum t] ->
  @local_map s m1 i :o @local_map t m2 j = @local_map t m2 j :o @local_map s m1 i.
Proof.
elim: t j=>[|a|t IH u IHu|n g b IH|n g b IH] j /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- exact: local_map_atom.
- apply: IH; exact: fintype.disjointWr (finset.subsetUl _ _) Hdis.
Qed.

Lemma eval_reads A (e : expression A) R m t :
  (expression_reads e `<=` R)%classic ->
  ClassicalFootprint.agree_on R m t -> eval e m = eval e t.
Proof.
move=>HR Hmt; apply: ClassicalFootprint.eval_local=>u x Hx.
apply: Hmt; exact: HR.
Qed.

Lemma atom_map_agree a m t i : ClassicalFootprint.agree_on (atom_reads a) m t ->
  @atom_map a m i = @atom_map a t i.
Proof.
case: a i=>[| |u x e|u x p|u q phi|u q U|u v x q M] i /= Hmt=>//.
- have Ep : eval (CL.probability_expression p) m = eval (CL.probability_expression p) t.
    apply: eval_reads Hmt; by move=>k Hk; right.
  change (eval (CL.probability_expression p) m i *: (\:1 : 'SO(Hq)) =
    eval (CL.probability_expression p) t i *: (\:1 : 'SO(Hq))).
  by rewrite Ep.
- by rewrite (eval_reads (fun k Hk => Hk) Hmt).
- by rewrite (eval_reads (fun k Hk => Hk) Hmt).
- have EM : eval M m = eval M t.
    apply: eval_reads Hmt; by move=>k Hk; right.
  rewrite !CL.measurement_branchE.
  change (liftfso (formso (tf2f q q (eval M m i))) =
    liftfso (formso (tf2f q q (eval M t i)))).
  by rewrite EM.
Qed.

Lemma local_map_agree s m t i : ClassicalFootprint.agree_on (statement_reads s) m t ->
  @local_map s m i = @local_map s t i.
Proof.
elim: s i=>[|a|s IH u IHu|n g b IH|n g b IH] i /= Hmt=>//.
- exact: atom_map_agree.
- apply: IH=>v x Hx; apply: Hmt; by left.
Qed.

Lemma memory_ext m t :
  (forall u (x : CL.variable u), (m.[x] = t.[x])%M) -> m = t.
Proof.
case: m=>m; case: t=>t; move=>H; congr CMem.
apply: functional_extensionality_dep=>u; apply/funext=>[[a b]].
exact: (H u (@CVar u a b)).
Qed.

Lemma updates_commute u v (x : CL.variable u) (y : CL.variable v) a b m :
  name_of x != name_of y ->
  ((m.[x <- a]).[y <- b] = (m.[y <- b]).[x <- a])%M.
Proof.
move=>Hxy; apply: memory_ext=>w z.
rewrite /cmset /cmget /cvtype /= /orapp.
case: eqP=>Euw; case: eqP=>Evw; rewrite ?eqxx //=.
case Exz: (cvname x == cvname z); case Eyz: (cvname y == cvname z)=>//.
exfalso; move/eqP: Hxy; apply.
apply/eqP; rewrite /name_of /CL.key xpair_eqE; apply/andP; split; apply/eqP.
- exact: (eq_trans Evw (esym Euw)).
- exact: (eq_trans (eqP Exz) (esym (eqP Eyz))).
Qed.


Lemma update_agree R u (x : CL.variable u) v m :
  ~ R (name_of x) -> ClassicalFootprint.agree_on R m (m.[x <- v])%M.
Proof.
move=>Hfresh t y Hy; apply: update_unchanged.
rewrite inE; apply/negP=>/eqP E; apply: Hfresh; by rewrite -E.
Qed.

Lemma eval_external A (e : expression A) R u (x : CL.variable u) v m :
  (expression_reads e `<=` R)%classic -> ~ R (name_of x) ->
  eval e (m.[x <- v])%M = eval e m.
Proof.
move=>Hsub Hfresh; symmetry; exact: eval_reads Hsub (update_agree v m Hfresh).
Qed.

Lemma atom_control_external a m u (x : CL.variable u) v i :
  ~ atom_reads a (name_of x) ->
  @atom_control a (m.[x <- v])%M i =
    ((@atom_control a m i).1, omap (fun t => (t.[x <- v])%M) (@atom_control a m i).2).
Proof.
case: a i=>[| |t y e|t y p|t q phi|t q U|t w y q M] i /= Hfresh=>//.
- have He : eval e (m.[x <- v])%M = eval e m.
    apply: (@eval_external _ e (atom_reads (AAssign y e)) u x v m); last exact Hfresh.
    by move=>k Hk; right.
  rewrite He; congr (Finished, Some _); apply: updates_commute.
  apply/negP=>/eqP E; apply: Hfresh; left; exact E.
- congr (Finished, Some _); apply: updates_commute.
  apply/negP=>/eqP E; apply: Hfresh; left; exact E.
- congr (Finished, Some _); apply: updates_commute.
  apply/negP=>/eqP E; apply: Hfresh; left; exact E.
Qed.

Lemma local_control_external s m u (x : CL.variable u) v i :
  ~ statement_reads s (name_of x) ->
  @local_control s (m.[x <- v])%M i =
    ((@local_control s m i).1, omap (fun t => (t.[x <- v])%M) (@local_control s m i).2).
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /= Hfresh=>//.
- exact: atom_control_external.
- have Hs : ~ statement_reads s (name_of x) by move=>Hs; apply: Hfresh; left.
  by rewrite (IH i Hs).
- have Eg : (fun j => eval (g j) (m.[x <- v])%M) = (fun j => eval (g j) m).
    apply/funext=>j; apply: (@eval_external _ (g j) _ u x v m _ Hfresh).
    move=>k Hk; exists j=>//; by left.
  rewrite Eg; by case: pickP.
- have Eg : (fun j => eval (g j) (m.[x <- v])%M) = (fun j => eval (g j) m).
    apply/funext=>j; apply: (@eval_external _ (g j) _ u x v m _ Hfresh).
    move=>k Hk; exists j=>//; by left.
  rewrite Eg; by case: pickP.
Qed.

Lemma local_map_external_update s m u (x : CL.variable u) v i :
  ~ statement_reads s (name_of x) ->
  @local_map s (m.[x <- v])%M i = @local_map s m i.
Proof.
move=>Hfresh; symmetry; apply: local_map_agree.
exact: update_agree.
Qed.


Local Open Scope fset_scope.
Definition store_outcome (xs : {fset classical_name}) m out :=
  out = None \/ out = Some m \/
  exists u (x : CL.variable u) v, name_of x \in xs /\ out = Some (m.[x <- v])%M.

Lemma store_outcome_weaken xs ys m out : xs `<=` ys ->
  store_outcome xs m out -> store_outcome ys m out.
Proof.
move=>/fsubsetP Hxy [H|[H|[u [x [v [Hx Hout]]]]]]; [by left|by right; left|].
right; right; exists u, x, v; split=>//; exact: Hxy.
Qed.

Lemma atom_store_outcome a m i :
  store_outcome (atom_changes a) m (@atom_control a m i).2.
Proof.
case: a i=>[| |u x e|u x p|u q phi|u q U|u v x q M] i /=;
  rewrite /store_outcome; try by right; left.
- by left.
- right; right; exists u, x, (eval e m); by rewrite inE.
- right; right; exists u, x, i; by rewrite inE.
- right; right; exists (QType u), x, i; by rewrite inE.
Qed.

Lemma local_store_outcome s m i :
  store_outcome (statement_changes s) m (@local_control s m i).2.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /=.
- by right; left.
- exact: atom_store_outcome.
- apply: store_outcome_weaken (IH i); exact: fsubsetUl.
- case: pickP=>[j Hj|Hnone]; [by right; left|by left].
- case: pickP=>[j Hj|Hnone]; by right; left.
Qed.

Definition local_store s i m := (@local_control s m i).2.

Lemma local_store_external s (i : local_index s) m u (x : CL.variable u) v :
  ~ statement_reads s (name_of x) ->
  @local_store s i (m.[x <- v])%M = omap (fun t => (t.[x <- v])%M) (@local_store s i m).
Proof. by move=>Hfresh; rewrite /local_store (@local_control_external s m u x v i Hfresh). Qed.

Definition store_compose (F G : cmem -> option cmem) m :=
  if F m is Some t then G t else None.

Lemma local_stores_commute s t (i : local_index s) (j : local_index t) m :
  (forall x, x \in statement_changes s -> ~ statement_reads t x) ->
  (forall x, x \in statement_changes t -> ~ statement_reads s x) ->
  [disjoint statement_changes s & statement_changes t] ->
  store_compose (@local_store s i) (@local_store t j) m =
  store_compose (@local_store t j) (@local_store s i) m.
Proof.
move=>Hst Hts Hdis.
have A := @local_store_outcome s m i.
have B := @local_store_outcome t m j.
change (store_outcome (statement_changes s) m (@local_store s i m)) in A.
change (store_outcome (statement_changes t) m (@local_store t j m)) in B.
rewrite /store_compose.
case: A=>[A|[A|[u [x [v [Hx A]]]]]];
case: B=>[B|[B|[w [y [z [Hy B]]]]]]; rewrite A B /=; try by rewrite ?A ?B.
- by rewrite (@local_store_external s i m w y z (Hts _ Hy)) A.
- by rewrite (@local_store_external s i m w y z (Hts _ Hy)) A.
- by rewrite (@local_store_external t j m u x v (Hst _ Hx)) B.
- by rewrite (@local_store_external t j m u x v (Hst _ Hx)) B.
- rewrite (@local_store_external t j m u x v (Hst _ Hx)) B
    (@local_store_external s i m w y z (Hts _ Hy)) A /=.
  congr (Some _); apply: updates_commute.
  apply/negP=>/eqP E; move/fdisjointP: Hdis=>/(_ _ Hx).
  by rewrite -E Hy.
Qed.

End DistributedInterchange.
