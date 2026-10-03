(* Expression supports and store locality for the inherited cqwhile syntax. *)
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
From quantum.example.classical Require Import state language operational footprint.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Module ClassicalLocality.
Import ClassicalLanguage ClassicalFootprint ClassicalOperational.
Local Notation Hq := 'H[msys]_finset.setT.

Definition remaining_writes (c : option command) :=
  if c is Some c then writes c else [::].

Definition unchanged (xs : seq identifier) (s t : store) :=
  forall u (x : variable u), key x \notin xs -> (s.[x] = t.[x])%M.

Lemma unchanged_refl xs s : unchanged xs s s.
Proof. by move=>u x _. Qed.

Lemma update_unchanged u (x : variable u) v s :
  unchanged [:: key x] s (s.[x <- v])%M.
Proof.
move=>t y; rewrite inE /key xpair_eqE negb_and=>/orP[ne|ne]; symmetry.
- apply: get_set_ne; left; move=>E; move: ne.
  by rewrite /cvtype in E; rewrite E eqxx.
- apply: get_set_ne; right; by rewrite eq_sym.
Qed.

Lemma step_remaining_writes c s r c' s' r' (d : step c s r c' s' r') :
  {subset remaining_writes c' <= writes c}.
Proof.
induction d; rewrite /remaining_writes /=; move=>k; rewrite ?in_nil //.
- by rewrite mem_cat=>->; rewrite orbT.
- rewrite !mem_cat=>/orP[H|H]; apply/orP; [left; exact: IHd | by right].
- by rewrite mem_cat=>->.
- by rewrite mem_cat=>->; rewrite orbT.
- by rewrite mem_cat orbb.
Qed.

Lemma step_unchanged c s r c' s' r' (d : step c s r c' s' r') :
  unchanged (writes c) s s'.
Proof.
induction d; try exact: unchanged_refl.
- exact: update_unchanged.
- exact: update_unchanged.
- exact: update_unchanged.
- move=>u x; rewrite /= mem_cat negb_or=>/andP[Hx _]; exact: IHd.
- move=>u x; rewrite /= mem_cat negb_or=>/andP[Hx _]; exact: IHd.
Qed.

Lemma terminates_unchanged c s r s' r' (d : terminates c s r s' r') :
  unchanged (writes c) s s'.
Proof.
elim: d=>[c0 s0 r0 s1 r1 st|c0 c1 s0 r0 s1 r1 s2 r2 st tail IH].
- exact: step_unchanged st.
- move=>u x Hx; transitivity (s1.[x])%M.
  + exact (@step_unchanged c0 s0 r0 (Some c1) s1 r1 st u x Hx).
  + apply: IH; apply/negP=>H; move/negP: Hx; apply.
    exact (@step_remaining_writes c0 s0 r0 (Some c1) s1 r1 st (key x) H).
Qed.

Lemma route_unchanged rt c s r s' r' :
  eval_route rt c (s,r) = Some (s',r') -> unchanged (writes c) s s'.
Proof. move=>H; exact: terminates_unchanged (eval_route_sound H). Qed.

Lemma terminates_preserves_expression A (e : expression A) c s r s' r' :
  (forall k, expression_variables e k -> k \notin writes c) ->
  terminates c s r s' r' -> eval e s = eval e s'.
Proof.
move=>fresh d; apply: eval_local=>u x Hx.
exact (@terminates_unchanged c s r s' r' d u x (fresh (key x) Hx)).
Qed.

End ClassicalLocality.
