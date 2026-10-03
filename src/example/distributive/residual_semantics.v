(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)
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
From Stdlib Require List.
From quantum.example.distributive Require Import language operational sequentialization guarded_rules.
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module DistributedResidualSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Definition control_command (pc : control) :=
  if pc is Executing s then translate_statement s else CL.Skip.
Definition active_program n (indices : seq 'I_n) (pc : 'I_n -> control) tail :=
  foldr (fun i rest => CL.Sequence (control_command (pc i)) rest) tail indices.
Definition network_tail n (p : 'I_n -> process) :=
  CL.Sequence
    (CL.While (guards_any [seq bc.1 | bc <- rendezvous_commands p])
      (conditional_chain (rendezvous_commands p)))
    (CL.Conditional (termination_guard p) CL.Skip CL.Abort).
Definition residual_command n (p : 'I_n -> process) pc :=
  active_program (enum 'I_n) pc (network_tail p).

Lemma active_program_cat n (pc : 'I_n -> control) xs ys tail :
  active_program (xs ++ ys) pc tail = active_program xs pc (active_program ys pc tail).
Proof. exact: foldr_cat. Qed.

Lemma active_program_idle n (pc : 'I_n -> control) indices tail :
  (forall i, i \in indices -> control_command (pc i) = CL.Skip) ->
  CL.denote (active_program indices pc tail) = CL.denote tail.
Proof.
elim: indices=>[|i indices IH] //= H.
have Hi : control_command (pc i) = CL.Skip by apply: H; rewrite inE eqxx.
change (CL.denote (CL.Sequence (control_command (pc i)) (active_program indices pc tail)) = CL.denote tail).
rewrite Hi CL.denote_skip_left; apply: IH=>j Hj; apply: H; by rewrite inE Hj orbT.
Qed.

Lemma active_program_prefix n (pc : 'I_n -> control) xs ys tail :
  (forall i, i \in xs -> control_command (pc i) = CL.Skip) ->
  CL.denote (active_program (xs ++ ys) pc tail) = CL.denote (active_program ys pc tail).
Proof. rewrite active_program_cat; exact: active_program_idle. Qed.

Lemma active_program_fold n (pc : 'I_n -> control) indices tail :
  CL.denote (active_program indices pc tail) =
  CL.denote (CL.Sequence
    (foldr CL.Sequence CL.Skip [seq control_command (pc i) | i <- indices]) tail).
Proof.
elim: indices=>[|i indices IH].
- change (CL.denote tail = CL.denote (CL.Sequence CL.Skip tail)).
  by rewrite CL.denote_skip_left.
- change (slet (CL.denote (control_command (pc i)))
    (CL.denote (active_program indices pc tail)) =
    CL.denote (CL.Sequence (CL.Sequence (control_command (pc i))
      (foldr CL.Sequence CL.Skip [seq control_command (pc j) | j <- indices])) tail)).
  by rewrite CL.denote_sequenceA /= IH.
Qed.

Lemma residual_initial n (p : 'I_n -> process) :
  CL.denote (residual_command p (fun i => Executing (initialization (p i)))) =
  CL.denote (successful_sequentialize p).
Proof.
rewrite /residual_command active_program_fold /successful_sequentialize /sequentialize
  CL.denote_sequenceA /network_tail.
by [].
Qed.

Lemma residual_idle n (p : 'I_n -> process) pc :
  (forall i, pc i = Waiting \/ pc i = Stopped) ->
  CL.denote (residual_command p pc) = CL.denote (network_tail p).
Proof.
move=>H; apply: active_program_idle=>i _; case: (H i)=>->; by [].
Qed.

Definition residual_state n (p : 'I_n -> process) (c : global_configuration n) : state :=
  match c.1.2 with
  | None => CQState.bottom
  | Some m =>
      match asboolP (c.2 \is denlf) with
      | ReflectT H => CQKernel.apply (CL.denote (residual_command p c.1.1))
          (CQState.point m (DenLf_Build H))
      | ReflectF _ => CQState.bottom
      end
  end.

Lemma residual_stateE n (p : 'I_n -> process) pc m rho out : rho \is denlf ->
  residual_state p (global_config pc (Some m) rho) out =
  CL.denote (residual_command p pc) m out rho.
Proof.
move=>Hr; rewrite /residual_state /=; case: asboolP=>[H|H]; last by exfalso; apply: H.
exact: CQKernel.apply_point.
Qed.

Lemma residual_state_bound n (p : 'I_n -> process) c out :
  `|residual_state p c out| <= 1.
Proof.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
apply: denlf_trlf; exact: CQState.component_density.
Qed.

Lemma residual_initial_state n (p : 'I_n -> process) m (rho : 'FD(Hq)) :
  residual_state p (initial_configuration p m rho) =
  CQKernel.apply (CL.denote (successful_sequentialize p)) (CQState.point m rho).
Proof.
apply/vdistrP=>out; rewrite residual_stateE ?is_denlf // residual_initial.
by rewrite CQKernel.apply_point.
Qed.

Lemma control_after_local p s : control_command (after_local p s) = translate_statement s.
Proof. case: s=>//=; by case: branch_count. Qed.

Lemma active_program_ext n (pc pc' : 'I_n -> control) indices tail :
  (forall i, i \in indices -> control_command (pc i) = control_command (pc' i)) ->
  active_program indices pc tail = active_program indices pc' tail.
Proof.
elim: indices=>[|i indices IH] //= H.
change (CL.Sequence (control_command (pc i)) (active_program indices pc tail) =
  CL.Sequence (control_command (pc' i)) (active_program indices pc' tail)).
congr CL.Sequence.
- apply: H; by rewrite inE eqxx.
- apply: IH=>j Hj; apply: H; by rewrite inE Hj orbT.
Qed.

Lemma active_program_replace n (pc : 'I_n -> control) indices i ctl tail :
  i \notin indices ->
  active_program indices (replace pc i ctl) tail = active_program indices pc tail.
Proof.
move=>Hi; apply: active_program_ext=>j Hj; rewrite replace_other //.
apply/negP=>/eqP E; subst j; by move: Hi; rewrite Hj.
Qed.

Lemma active_program_focus n (pc : 'I_n -> control) xs i ys (p : process) s tail :
  i \notin xs -> i \notin ys ->
  (forall j, j \in xs -> control_command (pc j) = CL.Skip) ->
  CL.denote (active_program (xs ++ i :: ys) (replace pc i (after_local p s)) tail) =
  CL.denote (CL.Sequence (translate_statement s) (active_program ys pc tail)).
Proof.
move=>Hx Hy Hprefix.
have Hnew j : j \in xs -> control_command (replace pc i (after_local p s) j) = CL.Skip.
  move=>Hj.
  have Hji : j != i by apply/negP=>/eqP E; subst j; move: Hx; rewrite Hj.
  rewrite (replace_other _ _ Hji); exact: Hprefix Hj.
rewrite (@active_program_prefix n (replace pc i (after_local p s)) xs (i :: ys) tail Hnew).
change (CL.denote (CL.Sequence (control_command (replace pc i (after_local p s) i))
  (active_program ys (replace pc i (after_local p s)) tail)) =
  CL.denote (CL.Sequence (translate_statement s) (active_program ys pc tail))).
by rewrite replace_same control_after_local
  (@active_program_replace n pc ys i (after_local p s) tail Hy).
Qed.

Fixpoint first_active n (indices : seq 'I_n) (pc : 'I_n -> control) :=
  if indices is i :: rest then
    if pc i is Executing s then Some (i,s) else first_active rest pc
  else None.

Lemma first_active_some n indices (pc : 'I_n -> control) i s :
  first_active indices pc = Some (i,s) ->
  exists xs ys, indices = xs ++ i :: ys /\ pc i = Executing s /\
    forall j, j \in xs -> control_command (pc j) = CL.Skip.
Proof.
elim: indices=>[|j indices IH] //=.
case Ej: (pc j)=>[t| |] /= H.
- case: H=>[= <- <-]; exists [::],indices; split=>//; split=>//.
- have [xs [ys [E [Hi Hp]]]] := IH H.
  exists (j::xs),ys; split; first by rewrite /= E.
  split=>// k; rewrite inE=>/orP[/eqP->|Hk]; first by rewrite Ej.
  exact: Hp Hk.
- have [xs [ys [E [Hi Hp]]]] := IH H.
  exists (j::xs),ys; split; first by rewrite /= E.
  split=>// k; rewrite inE=>/orP[/eqP->|Hk]; first by rewrite Ej.
  exact: Hp Hk.
Qed.

Lemma first_active_none n indices (pc : 'I_n -> control) :
  first_active indices pc = None ->
  forall i, i \in indices -> pc i = Waiting \/ pc i = Stopped.
Proof.
elim: indices=>[|j indices IH] //=.
case Ej: (pc j)=>[s| |] //= H i; rewrite inE=>/orP[/eqP->|Hi].
- by left.
- exact: IH H i Hi.
- by right.
- exact: IH H i Hi.
Qed.

Lemma uniq_focus (T : eqType) (xs : seq T) i ys :
  uniq (xs ++ i :: ys) -> i \notin xs /\ i \notin ys.
Proof.
rewrite cat_uniq /= negb_or=>/and3P[_ /andP[Hi _] /andP[Hj _]]; by split.
Qed.

Lemma residual_local_focus n (p : 'I_n -> process) pc i s :
  first_active (enum 'I_n) pc = Some (i,s) -> exists tail,
    CL.denote (residual_command p pc) =
      CL.denote (CL.Sequence (translate_statement s) tail) /\
    forall t,
      CL.denote (residual_command p (replace pc i (after_local (p i) t))) =
        CL.denote (CL.Sequence (translate_statement t) tail).
Proof.
move=>H; have [xs [ys [E [Hi Hp]]]] := first_active_some H.
have HU : uniq (xs ++ i :: ys) by rewrite -E enum_uniq.
have [Hx Hy] := uniq_focus HU.
exists (active_program ys pc (network_tail p)); split.
- have Ecmd : residual_command p pc =
      residual_command p (replace pc i (after_local (p i) s)).
    apply: active_program_ext=>j Hj; rewrite /replace.
    case Ej: (j == i); last by [].
    move/eqP: Ej=>->; by rewrite Hi control_after_local.
  rewrite Ecmd /residual_command E; exact: active_program_focus Hx Hy Hp.
- move=>t; rewrite /residual_command E; exact: active_program_focus Hx Hy Hp.
Qed.

End DistributedResidualSemantics.
