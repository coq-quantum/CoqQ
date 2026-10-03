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
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import footprint.
From quantum.example.distributive Require Import language operational scheduler.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedLocalActions.
Import DistributedLanguage DistributedOperational DistributedScheduler.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma pick_guard_unique n (g : 'I_n -> expression bool) m i :
  exclusive g -> eval (g i) m -> [pick j | eval (g j) m] = Some i.
Proof.
move=>Hex Hi; case: pickP=>[j Hj|Hnone].
  by rewrite (Hex m j i Hj Hi).
by move: (Hnone i); rewrite Hi.
Qed.

Lemma pick_guard_none n (g : 'I_n -> expression bool) m :
  [forall i, ~~ eval (g i) m] -> [pick j | eval (g j) m] = None.
Proof.
move=>/forallP Hnone; case: pickP=>// j Hj.
by move: (Hnone j); rewrite Hj.
Qed.

Definition atom_successor (a : atom) m rho : family local_configuration :=
  match a with
  | ASkip => certain (local_config Finished (Some m) rho)
  | AAbort => certain (local_config Finished None rho)
  | AAssign _ x e => certain (local_config Finished (Some (m.[x <- eval e m])%M) rho)
  | ARandom t x mu => @Family _ (CL.value t) (fun v => CL.probability_mass mu m v)
      (fun v => local_config Finished (Some (m.[x <- v])%M) rho)
  | AInitial _ q phi => certain (local_config Finished (Some m)
      (liftfso (initialso (tv2v q (eval phi m))) rho))
  | AUnitary _ q U => certain (local_config Finished (Some m)
      (liftfso (formso (tf2f q q (eval U m))) rho))
  | AMeasure _ _ x q M => measurement_branch x q M m rho
  end.

Fixpoint local_successor (s : statement) m rho : family local_configuration :=
  match s with
  | Finished => certain (local_config Finished (Some m) rho)
  | Atomic a => atom_successor a m rho
  | Sequence s t => fmap (append_configuration t) (local_successor s m rho)
  | Alternative n g b =>
      if [pick j | eval (g j) m] is Some j
      then certain (local_config (b j) (Some m) rho)
      else certain (local_config Finished None rho)
  | Repetition n g b =>
      if [pick j | eval (g j) m] is Some j
      then certain (local_config (Sequence (b j) (Repetition g b)) (Some m) rho)
      else certain (local_config Finished (Some m) rho)
  end.

Lemma local_step_canonical c mu : local_step c mu -> statement_wf c.1.1 ->
  forall m, c.1.2 = Some m -> mu = local_successor c.1.1 m c.2.
Proof.
move=>d; induction d; move=>Hwf m0 [= <-] //=.
- by rewrite (IHd (proj1 Hwf) m erefl).
- by rewrite (pick_guard_unique (proj1 Hwf) H).
- by rewrite (pick_guard_none H).
- by rewrite (pick_guard_unique (proj1 Hwf) H).
- by rewrite (pick_guard_none H).
Qed.

Lemma local_step_deterministic s m rho mu nu : statement_wf s ->
  local_step (local_config s (Some m) rho) mu ->
  local_step (local_config s (Some m) rho) nu -> mu = nu.
Proof.
move=>Hwf Hmu Hnu.
by rewrite (local_step_canonical Hmu Hwf erefl) (local_step_canonical Hnu Hwf erefl).
Qed.


Lemma append_reads s t :
  (statement_reads (append s t) `<=` (statement_reads s `|` statement_reads t))%classic.
Proof.
case: s=>[|a|s1 s2|n g b|n g b] /= x Hx.
- by right.
- exact Hx.
- exact Hx.
- exact Hx.
- exact Hx.
Qed.

Lemma local_step_reads c mu : local_step c mu -> forall i,
  (statement_reads (branch_value mu i).1.1 `<=` statement_reads c.1.1)%classic.
Proof.
move=>d; induction d; cbn [local_config certain branch_value fmap];
  move=>outcome z; try by [].
- move=>/append_reads [Hx|Hx].
  + left; exact: (IHd outcome z Hx).
  + by right.
- move=>Hx; exists i=>//; by right.
- move=>[Hx|Hx]; last exact Hx.
  exists i=>//; by right.
Qed.

Lemma append_quantum s t :
  (statement_quantum (append s t) :<=: statement_quantum s :|: statement_quantum t)%SET.
Proof. by case: s=>//=; rewrite finset.set0U. Qed.

Lemma branch_quantum_subset n (b : 'I_n -> statement) i :
  (statement_quantum (b i) :<=: \bigcup_j statement_quantum (b j))%SET.
Proof. apply/fintype.subsetP=>x Hx; apply/finset.bigcupP; by exists i. Qed.

Lemma local_step_quantum c mu : local_step c mu -> forall i,
  (statement_quantum (branch_value mu i).1.1 :<=: statement_quantum c.1.1)%SET.
Proof.
move=>d; induction d; cbn [local_config certain branch_value fmap];
  move=>outcome; try exact: finset.sub0set.
- apply: fintype.subset_trans (append_quantum _ _) _.
  by rewrite finset.subUset (fintype.subset_trans (IHd outcome) (finset.subsetUl _ _)) (finset.subsetUr _ _).
- exact: branch_quantum_subset.
- by rewrite /= finset.subUset branch_quantum_subset subxx.
Qed.


Local Open Scope fset_scope.
Definition unchanged (xs : {fset classical_name}) (s t : cmem) :=
  forall u (x : CL.variable u), name_of x \notin xs -> (s.[x] = t.[x])%M.

Lemma unchanged_refl xs s : unchanged xs s s.
Proof. by move=>u x _. Qed.

Lemma update_unchanged u (x : CL.variable u) v s :
  unchanged [fset name_of x] s (s.[x <- v])%M.
Proof.
move=>t y; rewrite inE /name_of /CL.key xpair_eqE negb_and=>/orP[ne|ne]; symmetry.
- apply: get_set_ne; left; move=>E; move: ne.
  by rewrite /cvtype in E; rewrite E eqxx.
- apply: get_set_ne; right; by rewrite eq_sym.
Qed.

Lemma local_step_unchanged c mu : local_step c mu -> forall outcome s t,
  c.1.2 = Some s -> (branch_value mu outcome).1.2 = Some t ->
  unchanged (statement_changes c.1.1) s t.
Proof.
move=>d; induction d; move=>outcome s0 t0 [= <-];
  cbn [local_config certain branch_value fmap measurement_branch append_configuration];
  try by move=>[= <-]; apply: unchanged_refl.
- by [].
- move=>[= <-]; exact: update_unchanged.
- move=>[= <-]; exact: update_unchanged.
- move=>[= <-]; exact: update_unchanged.
- move=>Ht u x; rewrite /= in_fsetU negb_or=>/andP[Hx _].
  exact: (IHd outcome m t0 erefl Ht u x Hx).
- by [].
Qed.

Lemma local_step_preserves_expression A (e : expression A) s m rho mu outcome t :
  (forall k, expression_reads e k -> k \notin statement_changes s) ->
  local_step (local_config s (Some m) rho) mu ->
  (branch_value mu outcome).1.2 = Some t -> eval e m = eval e t.
Proof.
move=>Hfresh Hstep Hout; apply: ClassicalFootprint.eval_local=>u x Hx.
apply: (local_step_unchanged Hstep erefl Hout).
exact: Hfresh.
Qed.

End DistributedLocalActions.
