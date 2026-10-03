(* Distributive: hoare. See README.md and PROOF_NOTES.md. *)
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
From quantum.example.distributive Require Import language operational confluence semantics sequentialization.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module DistributedGuardedRules.
(* Independent guarded-command rules, quantum ranking assertions, and
   soundness/completeness for their shared-language translation. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Implicit Types P Q R : assertion.

Lemma conditional_chain_bound total P Q (bs : seq (expression bool * CL.command)) m :
  List.Forall (fun bc : expression bool * CL.command => eval bc.1 m ->
    (P m : 'End(Hq)) ⊑ CQHoare.pre total bc.2 Q m) bs ->
  (~~ has (fun bc => eval bc.1 m) bs ->
    (P m : 'End(Hq)) ⊑ CQHoare.pre total CL.Abort Q m) ->
  (P m : 'End(Hq)) ⊑ CQHoare.pre total (conditional_chain bs) Q m.
Proof.
elim: bs=>[|[b c] bs IH] /=.
- by move=>_ Hnone; apply: Hnone.
- move=>/List.Forall_cons_iff [Hhead Htail] Hnone.
  rewrite CQHoare.pre_conditional /conditional /= -/(eval b m); case Eb: (eval b m).
  + exact: Hhead Eb.
  + apply: IH Htail _=>Hbs; apply: Hnone; by rewrite /= Eb Hbs.
Qed.

Lemma conditional_chain_valid total P Q (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command => CQHoare.valid total (mask (eval bc.1) P) bc.2 Q) bs ->
  (forall m, ~~ has (fun bc => eval bc.1 m) bs ->
    (P m : 'End(Hq)) ⊑ CQHoare.pre total CL.Abort Q m) ->
  CQHoare.valid total P (conditional_chain bs) Q.
Proof.
move=>Hbranches Hnone; apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>m.
apply: conditional_chain_bound; last exact: Hnone.
elim: Hbranches=>[|[b c] rest Hvalid Htail IH]; constructor=>// Hb.
move: ((proj1 (CQHoare.valid_iff _ _ _ _) Hvalid) m).
by rewrite /mask /= Hb.
Qed.

Lemma conditional_chain_upper total Q R
    (bs : seq (expression bool * CL.command)) m :
  List.Forall (fun bc : expression bool * CL.command => eval bc.1 m ->
    (CQHoare.pre total bc.2 Q m : 'End(Hq)) ⊑ R m) bs ->
  has (fun bc => eval bc.1 m) bs ->
  (CQHoare.pre total (conditional_chain bs) Q m : 'End(Hq)) ⊑ R m.
Proof.
elim: bs=>[|[b c] bs IH] //=.
move=>/List.Forall_cons_iff [Hhead Htail].
rewrite CQHoare.pre_conditional /conditional /= -/(eval b m).
case Eb: (eval b m)=>/= Hany; first exact: Hhead Eb.
exact: IH Htail Hany.
Qed.

Lemma mapped_branches_valid total P Q n (g : 'I_n -> expression bool) b :
  (forall i, CQHoare.valid total (mask (eval (g i)) P) (b i) Q) ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total (mask (eval bc.1) P) bc.2 Q)
    [seq (g i,b i) | i <- enum 'I_n].
Proof.
move=>H; elim: (enum 'I_n)=>[|i indices IH] /=; constructor=>//; exact: H.
Qed.

Lemma alternative_partial P Q n (g : 'I_n -> expression bool) b :
  (forall i, CQHoare.valid false (mask (eval (g i)) P) (b i) Q) ->
  CQHoare.valid false P
    (conditional_chain [seq (g i,b i) | i <- enum 'I_n]) Q.
Proof.
move=>H; apply: conditional_chain_valid; first exact: mapped_branches_valid.
move=>m _; change ((P m : 'End(Hq)) ⊑ wlp abort_sem Q m).
by rewrite wlp_abort; apply: obsf_le1.
Qed.

Lemma alternative_total P Q n (g : 'I_n -> expression bool) b :
  semantic_le P (mask (enabled g) semantic_top) ->
  (forall i, CQHoare.valid true (mask (eval (g i)) P) (b i) Q) ->
  CQHoare.valid true P
    (conditional_chain [seq (g i,b i) | i <- enum 'I_n]) Q.
Proof.
move=>Hcover H; apply: conditional_chain_valid; first exact: mapped_branches_valid.
move=>m; rewrite has_map=>Hnone.
change ((P m : 'End(Hq)) ⊑ wp abort_sem Q m).
rewrite wp_abort; move: (Hcover m); by rewrite /mask /enabled (negbTE Hnone).
Qed.

Lemma guarded_chain_valid total P Q n (g : 'I_n -> expression bool) b :
  (forall i, CQHoare.valid total (mask (eval (g i)) P) (b i) Q) ->
  CQHoare.valid total (mask (enabled g) P)
    (conditional_chain [seq (g i,b i) | i <- enum 'I_n]) Q.
Proof.
move=>H; apply: conditional_chain_valid.
- apply: mapped_branches_valid=>i.
  apply: (@CQHoare.valid_consequence total (mask (eval (g i)) P) Q
    (mask (eval (g i)) (mask (enabled g) P)) Q (b i)); last exact: H.
  + move=>m; rewrite /mask; case: (eval (g i) m)=>//.
    by case: (enabled g m)=>//; apply: obsf_ge0.
  + exact: semantic_le_refl.
- move=>m; rewrite has_map=>Hnone; rewrite /mask /enabled (negbTE Hnone).
  exact: obsf_ge0.
Qed.

Record ranking P n (g : 'I_n -> expression bool) (b : 'I_n -> statement) := Ranking {
  ranking_assertion : nat -> assertion;
  ranking_decreases : forall k,
    semantic_le (ranking_assertion k.+1) (ranking_assertion k);
  ranking_initial : semantic_le P (ranking_assertion 0%N);
  ranking_zero : forall m,
    ((fun k => (ranking_assertion k m : 'End(Hq))) @ \oo --> 0)%classic;
  ranking_step : forall k i,
    semantic_le
      (mask (eval (g i)) (CQHoare.wp_command (translate_statement (b i)) (ranking_assertion k)))
      (ranking_assertion k.+1)
}.

Lemma ranking_transfer P n (g : 'I_n -> expression bool) b :
  ranking P g b ->
  CQHoare.ranking P (loop_guard g)
    (conditional_chain [seq (g i,translate_statement (b i)) | i <- enum 'I_n]).
Proof.
move=>[r dec ini zero step]; apply: (CQHoare.Ranking (ranking_assertion := r)).
- exact: dec.
- exact: ini.
- exact: zero.
move=>k m.
rewrite /mask -/(eval (loop_guard g) m) eval_loop_guard.
case E: (enabled g m); last exact: obsf_ge0.
change ((CQHoare.pre true (conditional_chain
  [seq (g i,translate_statement (b i)) | i <- enum 'I_n]) (r k) m : 'End(Hq)) ⊑ r k.+1 m).
apply: conditional_chain_upper; last by rewrite has_map.
elim: (enum 'I_n)=>[|i indices IH] /=; constructor=>// Hi.
by move: (step k i m); rewrite /mask Hi.
Qed.

Lemma repetition_partial P n (g : 'I_n -> expression bool) b :
  (forall i, CQHoare.valid false (mask (eval (g i)) P) (translate_statement (b i)) P) ->
  CQHoare.valid false P (translate_statement (Repetition g b))
    (mask (predC (enabled g)) P).
Proof.
move=>H; change (CQHoare.valid false P
  (CL.While (loop_guard g) (conditional_chain
    [seq (g i,translate_statement (b i)) | i <- enum 'I_n]))
  (mask (predC (enabled g)) P)).
have E : esem (loop_guard g) = enabled g.
  by apply/funext=>m; exact: eval_loop_guard.
rewrite -E; apply: CQHoare.valid_while_partial; rewrite E.
exact: guarded_chain_valid.
Qed.

Lemma repetition_total P n (g : 'I_n -> expression bool) b :
  (forall i, CQHoare.valid true (mask (eval (g i)) P) (translate_statement (b i)) P) ->
  ranking P g b ->
  CQHoare.valid true P (translate_statement (Repetition g b))
    (mask (predC (enabled g)) P).
Proof.
move=>H Hr; change (CQHoare.valid true P
  (CL.While (loop_guard g) (conditional_chain
    [seq (g i,translate_statement (b i)) | i <- enum 'I_n]))
  (mask (predC (enabled g)) P)).
have E : esem (loop_guard g) = enabled g.
  by apply/funext=>m; exact: eval_loop_guard.
rewrite -E; apply: CQHoare.valid_while_total.
- rewrite E; exact: guarded_chain_valid.
- exact: ranking_transfer Hr.
Qed.

Inductive derives : bool -> assertion -> statement -> assertion -> Prop :=
| DAtom total P a Q : CQHoare.derives total P (translate_atom a) Q ->
    derives total P (Atomic a) Q
| DSequence total P Q R s t : derives total P s Q -> derives total Q t R ->
    derives total P (Sequence s t) R
| DAlternativePartial P Q n (g : 'I_n -> expression bool) b :
    exclusive g -> (forall i, derives false (mask (eval (g i)) P) (b i) Q) ->
    derives false P (Alternative g b) Q
| DAlternativeTotal P Q n (g : 'I_n -> expression bool) b :
    exclusive g -> semantic_le P (mask (enabled g) semantic_top) ->
    (forall i, derives true (mask (eval (g i)) P) (b i) Q) ->
    derives true P (Alternative g b) Q
| DRepetitionPartial P n (g : 'I_n -> expression bool) b :
    exclusive g -> (forall i, derives false (mask (eval (g i)) P) (b i) P) ->
    derives false P (Repetition g b) (mask (predC (enabled g)) P)
| DRepetitionTotal P n (g : 'I_n -> expression bool) b :
    exclusive g -> (forall i, derives true (mask (eval (g i)) P) (b i) P) ->
    ranking P g b ->
    derives true P (Repetition g b) (mask (predC (enabled g)) P)
| DConsequence total P Q P' Q' s :
    semantic_le P' P -> semantic_le Q Q' -> derives total P s Q ->
    derives total P' s Q'.

Theorem derives_translate_sound total P s Q : derives total P s Q ->
  CQHoare.valid total P (translate_statement s) Q.
Proof.
move=>D; induction D.
- exact: CQHoare.derives_sound.
- exact: CQHoare.valid_sequence IHD1 IHD2.
- exact: alternative_partial.
- exact: alternative_total.
- exact: repetition_partial.
- exact: repetition_total.
- exact: (@CQHoare.valid_consequence total P Q P' Q' (translate_statement s) H H0 IHD).
Qed.

Lemma conditional_chain_pre_selected total Q n (g : 'I_n -> expression bool)
    (b : 'I_n -> CL.command) (indices : seq 'I_n) m i :
  exclusive g -> i \in indices -> eval (g i) m ->
  CQHoare.pre total (conditional_chain [seq (g j,b j) | j <- indices]) Q m =
  CQHoare.pre total (b i) Q m.
Proof.
move=>Hex; elim: indices=>[|j indices IH] //.
change (i \in j :: indices -> eval (g i) m ->
  CQHoare.pre total (CL.Conditional (g j) (b j)
    (conditional_chain [seq (g z,b z) | z <- indices])) Q m =
  CQHoare.pre total (b i) Q m).
rewrite inE=>/orP[/eqP E|Hi] Hgi.
- subst j; by rewrite CQHoare.pre_conditional /conditional -/(eval (g i) m) Hgi.
- rewrite CQHoare.pre_conditional /conditional -/(eval (g j) m).
  case Hgj: (eval (g j) m).
  + by rewrite (Hex m j i Hgj Hgi).
  + exact: IH Hi Hgi.
Qed.

Lemma conditional_chain_pre_none total Q
    (bs : seq (expression bool * CL.command)) m :
  ~~ has (fun bc => eval bc.1 m) bs ->
  CQHoare.pre total (conditional_chain bs) Q m = CQHoare.pre total CL.Abort Q m.
Proof.
elim: bs=>[|[b c] bs IH] //=.
rewrite negb_or=>/andP[Hb Hbs].
change (CQHoare.pre total (CL.Conditional b c (conditional_chain bs)) Q m =
  CQHoare.pre total CL.Abort Q m).
rewrite CQHoare.pre_conditional /conditional -/(eval b m) (negbTE Hb).
exact: IH Hbs.
Qed.

Lemma alternative_pre_branch total Q n (g : 'I_n -> expression bool) b i :
  exclusive g ->
  semantic_le (mask (eval (g i))
    (CQHoare.pre total (conditional_chain [seq (g j,b j) | j <- enum 'I_n]) Q))
    (CQHoare.pre total (b i) Q).
Proof.
move=>Hex m; rewrite /mask; case Ei: (eval (g i) m); last exact: obsf_ge0.
have Hi : i \in enum 'I_n by rewrite mem_enum.
by rewrite (@conditional_chain_pre_selected total Q n g b (enum 'I_n) m i Hex Hi Ei).
Qed.

Lemma alternative_pre_covered Q n (g : 'I_n -> expression bool) b :
  semantic_le (CQHoare.pre true
    (conditional_chain [seq (g i,b i) | i <- enum 'I_n]) Q)
    (mask (enabled g) semantic_top).
Proof.
move=>m; rewrite /mask; case E: (enabled g m); first exact: obsf_le1.
have Hnone : ~~ has (fun bc : expression bool * CL.command => eval bc.1 m)
    [seq (g i,b i) | i <- enum 'I_n] by rewrite has_map -/(enabled g m) E.
rewrite (conditional_chain_pre_none true Q Hnone).
change ((wp abort_sem Q m : 'End(Hq)) ⊑ 0).
by rewrite wp_abort.
Qed.

Lemma loop_pre_branch total Q n (g : 'I_n -> expression bool) b i :
  exclusive g ->
  semantic_le (mask (eval (g i))
    (CQHoare.pre total (translate_statement (Repetition g b)) Q))
    (CQHoare.pre total (translate_statement (b i))
      (CQHoare.pre total (translate_statement (Repetition g b)) Q)).
Proof.
move=>Hex m; rewrite /mask; case Ei: (eval (g i) m); last exact: obsf_ge0.
have Eg : enabled g m by apply/enabledP; exists i.
have W := congr1 (fun A : assertion => A m)
  (CQHoare.pre_while_unfold total (loop_guard g)
    (conditional_chain [seq (g j,translate_statement (b j)) | j <- enum 'I_n]) Q).
rewrite /conditional -/(eval (loop_guard g) m) eval_loop_guard Eg in W.
change ((CQHoare.pre total (CL.While (loop_guard g)
  (conditional_chain [seq (g j,translate_statement (b j)) | j <- enum 'I_n])) Q m : 'End(Hq)) ⊑
  CQHoare.pre total (translate_statement (b i))
    (CQHoare.pre total (translate_statement (Repetition g b)) Q) m).
rewrite W.
have Hi : i \in enum 'I_n by rewrite mem_enum.
by rewrite (@conditional_chain_pre_selected total
  (CQHoare.pre total (translate_statement (Repetition g b)) Q) n g
  (fun j => translate_statement (b j)) (enum 'I_n) m i Hex Hi Ei).
Qed.

Lemma loop_pre_post total Q n (g : 'I_n -> expression bool) b :
  semantic_le (mask (predC (enabled g))
    (CQHoare.pre total (translate_statement (Repetition g b)) Q)) Q.
Proof.
have E : esem (loop_guard g) = enabled g.
  by apply/funext=>m; exact: eval_loop_guard.
rewrite -E; exact: CQHoare.loop_invariant_post.
Qed.

Lemma loop_pre_ranking Q n (g : 'I_n -> expression bool) b : exclusive g ->
  ranking (CQHoare.pre true (translate_statement (Repetition g b)) Q) g b.
Proof.
move=>Hex.
have [r dec ini zero step] := CQHoare.loop_ranking (loop_guard g)
  (conditional_chain [seq (g i,translate_statement (b i)) | i <- enum 'I_n]) Q.
apply: (Ranking (ranking_assertion := r)).
- exact: dec.
- exact: ini.
- exact: zero.
move=>k i m; rewrite /mask; case Ei: (eval (g i) m); last exact: obsf_ge0.
have Eg : enabled g m by apply/enabledP; exists i.
have S := step k m.
rewrite /mask -/(eval (loop_guard g) m) eval_loop_guard Eg in S.
change (is_true ((CQHoare.pre true (conditional_chain
  [seq (g j,translate_statement (b j)) | j <- enum 'I_n]) (r k) m : 'End(Hq)) ⊑ r k.+1 m)) in S.
have Hi : i \in enum 'I_n by rewrite mem_enum.
by rewrite (@conditional_chain_pre_selected true (r k) n g
  (fun j => translate_statement (b j)) (enum 'I_n) m i Hex Hi Ei) in S.
Qed.

Theorem derives_pre total s : statement_wf s -> forall Q,
  derives total (CQHoare.pre total (translate_statement s) Q) s Q.
Proof.
elim: s=>[|a|s IHs t IHt|n g b IH|n g b IH] //=.
- move=>_ Q; apply: DAtom; exact: CQHoare.derives_pre.
- move=>[Hs Ht] Q; rewrite CQHoare.pre_sequence.
  apply: DSequence; [exact: IHs | exact: IHt].
- move=>[Hex Hwf] Q.
  have branches i : derives total
      (mask (eval (g i)) (CQHoare.pre total
        (conditional_chain [seq (g j,translate_statement (b j)) | j <- enum 'I_n]) Q))
      (b i) Q.
    apply: (@DConsequence total (CQHoare.pre total (translate_statement (b i)) Q) Q
      _ Q (b i)).
    + exact: alternative_pre_branch Hex.
    + exact: semantic_le_refl.
    + exact: IH.
  case E: total in branches *.
  + apply: DAlternativeTotal; [exact: Hex | exact: alternative_pre_covered | exact: branches].
  + apply: DAlternativePartial; [exact: Hex | exact: branches].
- move=>[Hex Hwf] Q.
  pose I := CQHoare.pre total (translate_statement (Repetition g b)) Q.
  apply: (@DConsequence total I (mask (predC (enabled g)) I) I Q (Repetition g b)).
  + exact: semantic_le_refl.
  + exact: loop_pre_post.
  + have branches i : derives total (mask (eval (g i)) I) (b i) I.
      apply: (@DConsequence total (CQHoare.pre total (translate_statement (b i)) I) I
        _ I (b i)).
      * exact: loop_pre_branch Hex.
      * exact: semantic_le_refl.
      * exact: IH.
    case E: total in I branches *.
    * apply: DRepetitionTotal; [exact: Hex | exact: branches | exact: loop_pre_ranking Hex].
    * apply: DRepetitionPartial; [exact: Hex | exact: branches].
Qed.

Theorem derives_translate_complete total P s Q : statement_wf s ->
  CQHoare.valid total P (translate_statement s) Q -> derives total P s Q.
Proof.
move=>Hwf /(proj1 (CQHoare.valid_iff _ _ _ _)) Hpre.
apply: (@DConsequence total (CQHoare.pre total (translate_statement s) Q) Q P Q s).
- exact: Hpre.
- exact: semantic_le_refl.
- exact: (@derives_pre total s Hwf Q).
Qed.

Theorem translate_sound_complete total P s Q : statement_wf s ->
  (derives total P s Q <-> CQHoare.valid total P (translate_statement s) Q).
Proof. move=>Hwf; split; [exact: derives_translate_sound | exact: derives_translate_complete]. Qed.
End DistributedGuardedRules.


Module DistributedLocalHoare.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedLocalIterations DistributedLocalIterationLimits CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition run s (rho : @CQState.state cmem Hq) :=
  CQKernel.apply (sem_lim (fun k => local_iter k s)) rho.

Theorem run_translate s rho : statement_wf s ->
  run s rho = CQHoare.run (translate_statement s) rho.
Proof. move=>Hs; by rewrite /run (local_iter_limit (or_intror Hs)). Qed.

Definition valid total (P : assertion) s Q :=
  forall rho : @CQState.state cmem Hq,
  if total then expect P rho <= expect Q (run s rho)
  else expect (complement Q) (run s rho) <= expect (complement P) rho.

Theorem valid_translate_iff total P s Q : statement_wf s ->
  (valid total P s Q <-> CQHoare.valid total P (translate_statement s) Q).
Proof.
move=>Hs; split=>H rho; have Hpoint := H rho.
- by rewrite (run_translate rho Hs) in Hpoint.
- by rewrite (run_translate rho Hs).
Qed.

Theorem derives_sound total P s Q : statement_wf s ->
  DistributedGuardedRules.derives total P s Q -> valid total P s Q.
Proof.
move=>Hs D; apply/(proj2 (@valid_translate_iff total P s Q Hs)).
exact: DistributedGuardedRules.derives_translate_sound D.
Qed.

Theorem derives_complete total P s Q : statement_wf s ->
  valid total P s Q -> DistributedGuardedRules.derives total P s Q.
Proof.
move=>Hs H; exact: (@DistributedGuardedRules.derives_translate_complete total P s Q Hs
  (proj1 (@valid_translate_iff total P s Q Hs) H)).
Qed.

Theorem sound_complete total P s Q : statement_wf s ->
  (DistributedGuardedRules.derives total P s Q <-> valid total P s Q).
Proof. move=>Hs; split; [exact: derives_sound Hs | exact: derives_complete Hs]. Qed.
End DistributedLocalHoare.


Module DistributedNetworkRules.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedGuardedRules CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Implicit Types P Q R : assertion.

Definition branch_guard (bs : seq (expression bool * CL.command)) :=
  guards_any [seq bc.1 | bc <- bs].

Lemma eval_branch_guard bs m :
  eval (branch_guard bs) m = has (fun bc => eval bc.1 m) bs.
Proof. by rewrite /branch_guard eval_guards_any has_map. Qed.

Lemma branches_strengthen total P P' Q (bs : seq (expression bool * CL.command)) :
  semantic_le P' P ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total (mask (eval bc.1) P) bc.2 Q) bs ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total (mask (eval bc.1) P') bc.2 Q) bs.
Proof.
move=>Hpre H; elim: H=>[|[g b] rest Hb Hrest IH]; constructor=>//.
apply: (@CQHoare.valid_consequence total (mask (eval g) P) Q
  (mask (eval g) P') Q b); last exact: Hb.
- move=>m; rewrite /mask; by case: (eval g m)=>//; apply: Hpre.
- exact: semantic_le_refl.
Qed.

Lemma guarded_list_valid total P Q (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total (mask (eval bc.1) P) bc.2 Q) bs ->
  CQHoare.valid total (mask (eval (branch_guard bs)) P) (conditional_chain bs) Q.
Proof.
move=>H; apply: conditional_chain_valid.
- apply: (branches_strengthen _ H)=>m; rewrite /mask.
  by case: (eval (branch_guard bs) m)=>//; apply: obsf_ge0.
- move=>m Hnone; rewrite /mask eval_branch_guard (negbTE Hnone).
  exact: obsf_ge0.
Qed.

Record list_ranking P (bs : seq (expression bool * CL.command)) := ListRanking {
  list_rank : nat -> assertion;
  list_rank_decreases : forall k, semantic_le (list_rank k.+1) (list_rank k);
  list_rank_initial : semantic_le P (list_rank 0%N);
  list_rank_zero : forall m,
    ((fun k => (list_rank k m : 'End(Hq))) @ \oo --> 0)%classic;
  list_rank_step : forall k,
    List.Forall (fun bc : expression bool * CL.command =>
      semantic_le (mask (eval bc.1) (CQHoare.wp_command bc.2 (list_rank k)))
        (list_rank k.+1)) bs
}.

Lemma list_ranking_transfer P bs : list_ranking P bs ->
  CQHoare.ranking P (branch_guard bs) (conditional_chain bs).
Proof.
move=>[r dec ini zero step]; apply: (CQHoare.Ranking (ranking_assertion := r)).
- exact: dec.
- exact: ini.
- exact: zero.
move=>k m; rewrite /mask -/(eval (branch_guard bs) m) eval_branch_guard.
case E: (has (fun bc : expression bool * CL.command => eval bc.1 m) bs);
  last exact: obsf_ge0.
change ((CQHoare.pre true (conditional_chain bs) (r k) m : 'End(Hq)) ⊑ r k.+1 m).
apply: conditional_chain_upper; last exact: E.
have H := step k; elim: H=>[|[g b] rest Hb Hrest IH]; constructor=>// Hg.
by move: (Hb m); rewrite /mask Hg.
Qed.

Lemma guarded_list_partial P (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid false (mask (eval bc.1) P) bc.2 P) bs ->
  CQHoare.valid false P (CL.While (branch_guard bs) (conditional_chain bs))
    (mask (predC (eval (branch_guard bs))) P).
Proof. move=>H; apply: CQHoare.valid_while_partial; exact: guarded_list_valid. Qed.

Lemma guarded_list_total P (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true (mask (eval bc.1) P) bc.2 P) bs ->
  list_ranking P bs ->
  CQHoare.valid true P (CL.While (branch_guard bs) (conditional_chain bs))
    (mask (predC (eval (branch_guard bs))) P).
Proof.
move=>H Hr; apply: CQHoare.valid_while_total; first exact: guarded_list_valid.
exact: list_ranking_transfer.
Qed.

Definition initialization_command n (p : 'I_n -> process) :=
  foldr CL.Sequence CL.Skip
    [seq translate_statement (initialization (p i)) | i <- enum 'I_n].
Definition blocked n (p : 'I_n -> process) := predC (eval (branch_guard (rendezvous_commands p))).
Definition network_ranking P n (p : 'I_n -> process) :=
  list_ranking P (rendezvous_commands p).

Lemma final_test_partial P Q b : semantic_le P Q ->
  CQHoare.valid false P (CL.Conditional b CL.Skip CL.Abort) (mask (eval b) Q).
Proof.
move=>HP; apply/(proj2 (CQHoare.valid_iff _ _ _ _)); rewrite CQHoare.pre_conditional=>m.
rewrite /conditional /mask -/(eval b m); case E: (eval b m).
- change ((P m : 'End(Hq)) ⊑ wlp skip_sem (mask (eval b) Q) m).
  by rewrite wlp_skip /mask E; exact: HP.
- change ((P m : 'End(Hq)) ⊑ wlp abort_sem (mask (eval b) Q) m).
  by rewrite wlp_abort; apply: obsf_le1.
Qed.

Lemma final_test_total P Q b : semantic_le P Q ->
  semantic_le P (mask (eval b) semantic_top) ->
  CQHoare.valid true P (CL.Conditional b CL.Skip CL.Abort) (mask (eval b) Q).
Proof.
move=>HP Hcover; apply/(proj2 (CQHoare.valid_iff _ _ _ _)); rewrite CQHoare.pre_conditional=>m.
rewrite /conditional /mask -/(eval b m); case E: (eval b m).
- change ((P m : 'End(Hq)) ⊑ wp skip_sem (mask (eval b) Q) m).
  by rewrite wp_skip /mask E; exact: HP.
- change ((P m : 'End(Hq)) ⊑ wp abort_sem (mask (eval b) Q) m).
  rewrite wp_abort; by move: (Hcover m); rewrite /mask E.
Qed.

Theorem distributed_partial P Q n (p : 'I_n -> process) :
  CQHoare.valid false P (initialization_command p) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid false (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
  CQHoare.valid false P (successful_sequentialize p) (mask (DistributedLanguage.term p) Q).
Proof.
move=>Hinit Hbranches.
have Et : eval (termination_guard p) = DistributedLanguage.term p.
  by apply/funext=>m; exact: eval_termination_guard.
rewrite -Et /successful_sequentialize.
apply: (CQHoare.valid_sequence (Q := mask (blocked p) Q)).
- apply: (CQHoare.valid_sequence Hinit); exact: guarded_list_partial.
- apply: final_test_partial=>m; rewrite /mask.
  by case: (blocked p m)=>//; apply: obsf_ge0.
Qed.

Theorem distributed_total P Q n (p : 'I_n -> process) :
  CQHoare.valid true P (initialization_command p) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
  network_ranking Q p ->
  semantic_le (mask (blocked p) Q) (mask (DistributedLanguage.term p) semantic_top) ->
  CQHoare.valid true P (successful_sequentialize p) (mask (DistributedLanguage.term p) Q).
Proof.
move=>Hinit Hbranches Hr Hdeadlock.
have Et : eval (termination_guard p) = DistributedLanguage.term p.
  by apply/funext=>m; exact: eval_termination_guard.
rewrite -Et /successful_sequentialize.
apply: (CQHoare.valid_sequence (Q := mask (blocked p) Q)).
- apply: (CQHoare.valid_sequence Hinit); exact: guarded_list_total.
- apply: final_test_total; last by rewrite Et.
  move=>m; rewrite /mask; by case: (blocked p m)=>//; apply: obsf_ge0.
Qed.

(* Network derivability uses the actual independent classical inference system
   in each translated initialization/communication-body premise. Operational
   distributed soundness additionally requires the sequentialization theorem. *)
Inductive derives : bool -> assertion -> forall n, ('I_n -> process) -> assertion -> Prop :=
| DDistributedPartial P Q n (p : 'I_n -> process) :
    CQHoare.derives false P (initialization_command p) Q ->
    List.Forall (fun bc : expression bool * CL.command =>
      CQHoare.derives false (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
    derives false P p (mask (DistributedLanguage.term p) Q)
| DDistributedTotal P Q n (p : 'I_n -> process) :
    CQHoare.derives true P (initialization_command p) Q ->
    List.Forall (fun bc : expression bool * CL.command =>
      CQHoare.derives true (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
    network_ranking Q p ->
    semantic_le (mask (blocked p) Q) (mask (DistributedLanguage.term p) semantic_top) ->
    derives true P p (mask (DistributedLanguage.term p) Q)
| DNetworkConsequence total P Q P' Q' n (p : 'I_n -> process) :
    semantic_le P' P -> semantic_le Q Q' -> derives total P p Q ->
    derives total P' p Q'.

Theorem derives_translate_sound total P n (p : 'I_n -> process) Q :
  derives total P p Q -> CQHoare.valid total P (successful_sequentialize p) Q.
Proof.
move=>D; induction D as
  [P0 Q0 n0 p0 Hinit Hbranches
  |P0 Q0 n0 p0 Hinit Hbranches Hr Hdeadlock
  |total0 P0 Q0 P1 Q1 n0 p0 Hpre Hpost D IHD].
- apply: distributed_partial; first exact: CQHoare.derives_sound Hinit.
  elim: Hbranches=>[|[g b] rest Hb Hrest IH]; constructor=>//; exact: CQHoare.derives_sound.
- apply: distributed_total; [exact: CQHoare.derives_sound Hinit | | exact: Hr | exact: Hdeadlock].
  elim: Hbranches=>[|[g b] rest Hb Hrest IH]; constructor=>//; exact: CQHoare.derives_sound.
- exact: (@CQHoare.valid_consequence total0 P0 Q0 P1 Q1 (successful_sequentialize p0) Hpre Hpost IHD).
Qed.
End DistributedNetworkRules.


Module DistributedGlobalPredicate.
(* Finite operational horizons as effects; see the D5 completeness argument. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedResidual DistributedResults DistributedSchedulerSemantics DistributedGlobalInstruments DistributedGlobalActions DistributedInstruments DistributedLocalActions DistributedProgress DistributedObservables DistributedLocalDiamond DistributedGlobalValue DistributedScheduler DistributedLocalCorrespondence CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.
Local Notation assertion := (@semantic_assertion cmem Hq).

Section Step.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Local Notation controls := ('I_n -> control).

Definition descriptor_valid pc m (d : descriptor n) :=
  exists a, enabled_descriptor p pc m a d /\ statement_wf (instruction d).

Definition selected_descriptor pc m : option (descriptor n) :=
  match pselect (exists d, descriptor_valid pc m d) with
  | left H => Some (projT1 (cid H))
  | right _ => None
  end.

Lemma selected_descriptor_some pc m d :
  selected_descriptor pc m = Some d -> descriptor_valid pc m d.
Proof.
rewrite /selected_descriptor; case: pselect=>[H|H] //.
by move=>[= <-]; exact: projT2 (cid H).
Qed.

Lemma selected_descriptor_none pc m : selected_descriptor pc m = None ->
  forall d, ~ descriptor_valid pc m d.
Proof.
rewrite /selected_descriptor; case: pselect=>[H|H] // _ d Hd.
by apply: H; exists d.
Qed.

Lemma descriptor_terminal pc m rho : configuration_owned p (global_config pc (Some m) rho) ->
  selected_descriptor pc m = None -> terminal p (global_config pc (Some m) rho).
Proof.
move=>Ho Hnone mu Hstep.
have [a Ha] := labeled_step_complete Hstep.
have [u [d [Eu [Hd [Hwf E]]]]] := labeled_step_descriptor Ho Ha.
change (Some m = Some u) in Eu; case: Eu=>Eum; subst u.
apply: (@selected_descriptor_none pc m Hnone d); by exists a.
Qed.

Definition observe (F : controls -> assertion) (c : global_configuration n) :=
  if c.1.2 is Some m then \Tr (F c.1.1 m \o c.2) else 0.

Definition descriptor_pre (F : controls -> assertion) (d : descriptor n) pc m : 'FO(Hq) :=
  wp (SemType (fun _ : unit => local_maps (instruction d) m))
    (fun a => if (@local_control (instruction d) m a).2 is Some u then
      F (update_control d (@local_control (instruction d) m a).1 pc) u else 0%:VF) tt.

Lemma descriptor_pre_observe F d pc m rho : rho \is den1lf ->
  \Tr (descriptor_pre F d pc m \o rho) =
  family_observe (descriptor_run d pc m rho) (observe F).
Proof.
move=>Hr; rewrite /descriptor_pre wp_pairing /descriptor_run
  (@local_realization (instruction d) m rho Hr) /family_observe /local_family /=.
apply: eq_sum=>a; rewrite local_mapsE /observe /descriptor_lift /local_config /=.
case E: (@local_control (instruction d) m a)=>[s [u|]] /=;
  last by rewrite linear0l linear0 mulr0.
have W := congr1 (fun A : 'End(Hq) => \Tr (F (update_control d s pc) u \o A))
  (weighted_normalized_output (@local_cp (instruction d) m a) Hr).
by rewrite linearZr /= linearZ /= in W; symmetry.
Qed.

Definition terminal_pre (Q : assertion) (pc : controls) m : 'FO(Hq) :=
  if [forall i, asbool (pc i = Stopped)] then Q m else 0%:VF.

Fixpoint horizon_pre k (Q : assertion) pc m : 'FO(Hq) :=
  if k is j.+1 then
    if selected_descriptor pc m is Some d then descriptor_pre (horizon_pre j Q) d pc m
    else terminal_pre Q pc m
  else terminal_pre Q pc m.

Lemma terminal_pre_observe Q pc m rho : rho \is denlf ->
  \Tr (terminal_pre Q pc m \o rho) =
  expect Q (successful_component (global_config pc (Some m) rho)).
Proof.
move=>Hr; rewrite /terminal_pre /successful_component /=.
case E: [forall i, asbool (pc i = Stopped)].
- case: asboolP=>[H|H]; last by exfalso; apply: H.
  by rewrite CQExpectation.expect_point.
- by rewrite CQHoare.expect_bottom linear0l linear0.
Qed.

End Step.
End DistributedGlobalPredicate.


Module DistributedNormalizedTests.
(* Compatibility interface for classical normalized validity tests. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Include CQNormalizedValidity.
End DistributedNormalizedTests.


Module DistributedNetworkPre.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules DistributedResidualSemantics DistributedSerialScheduler DistributedBoundarySemantics CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma xp_row total (K L : ClassicalSemantics.kernel) (Q : assertion) m :
  K m = L m -> xp total K Q m = xp total L Q m.
Proof.
move=>E; case: total; apply/val_inj.
- change ((wp K Q m : 'End(Hq)) = (wp L Q m : 'End(Hq))).
  by rewrite !wpE E.
- change ((wp K (complement Q) m : 'End(Hq))^⟂ =
    (wp L (complement Q) m : 'End(Hq))^⟂).
  by rewrite !wpE E.
Qed.

Lemma tail_pre_term total n (p : 'I_n -> process) (Q : assertion) m :
  DistributedLanguage.term p m -> CQHoare.pre total (network_tail p) Q m = Q m.
Proof.
move=>Ht; rewrite /CQHoare.pre (@xp_row total _ skip_sem Q m (network_tail_term Ht)).
by rewrite xp_skip.
Qed.

Lemma tail_pre_post total n (p : 'I_n -> process) (Q : assertion) :
  semantic_le (mask (DistributedLanguage.term p) (CQHoare.pre total (network_tail p) Q)) Q.
Proof.
move=>m; rewrite /mask; case Ht: (DistributedLanguage.term p m).
- by rewrite (tail_pre_term total Q Ht).
- exact: obsf_ge0.
Qed.

Lemma blocked_no_rendezvous n (p : 'I_n -> process) m : blocked p m -> no_rendezvous p m.
Proof.
change (~~ eval (branch_guard (rendezvous_commands p)) m -> no_rendezvous p m).
rewrite eval_branch_guard /no_rendezvous.
change (~~ has (fun bc : expression bool * CL.command => eval bc.1 m)
    (rendezvous_commands p) ->
  all (predC (fun bc : expression bool * CL.command => eval bc.1 m)) (rendezvous_commands p)).
by rewrite all_predC.
Qed.

Lemma tail_pre_deadlock n (p : 'I_n -> process) (Q : assertion) :
  semantic_le (mask (blocked p) (CQHoare.pre true (network_tail p) Q))
    (mask (DistributedLanguage.term p) semantic_top).
Proof.
move=>m; rewrite /mask; case Hb: (blocked p m); last exact: obsf_ge0.
case Ht: (DistributedLanguage.term p m); first exact: obsf_le1.
have E : ClassicalSemantics.denote (network_tail p) m = abort_sem m.
  by rewrite (network_tail_blocked (blocked_no_rendezvous Hb)) Ht.
rewrite /CQHoare.pre (@xp_row true _ abort_sem Q m E) /xp wp_abort.
exact: lexx.
Qed.

Lemma initialization_pre total n (p : 'I_n -> process) (Q : assertion) :
  CQHoare.pre total (successful_sequentialize p) Q =
  CQHoare.pre total (initialization_command p) (CQHoare.pre total (network_tail p) Q).
Proof.
by rewrite /successful_sequentialize /sequentialize /initialization_command /network_tail
  !CQHoare.pre_sequence.
Qed.
End DistributedNetworkPre.


Module DistributedHorizonExpectation.
(* Finite operational horizons as effects; see the D5 completeness argument. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate DistributedGlobalInstruments DistributedObservables CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Horizon.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).

Lemma approximant_collapse k c :
  @approximant P rho0 k (@collapse P rho0 c) = @approximant P rho0 k c.
Proof.
case: c=>[[pc [s|]] rho] //.
change (@approximant P rho0 k (@failure P rho0) =
  @approximant P rho0 k (global_config pc None rho)).
rewrite !approximant_terminal; try exact: failure_terminal.
by [].
Qed.

Lemma approximant_global_step c mu k (Hs : global_step p c mu)
    (Hr : c.2 \is den1lf) : configuration_owned p c ->
  @approximant P rho0 k.+1 c =
  CQStateMixture.mix (probability_distribution (global_step_probability Hs Hr))
    (fun i => @approximant P rho0 k (branch_value mu i)).
Proof.
move=>Ho; apply/vdistrP=>out.
rewrite CQStateMixture.mixE.
have Hp := @ProjectedGlobal P rho0 c mu (conj Hr Ho) Hs.
rewrite -(@approximant_advance P rho0 c _ k out Hp) /weighted_sum.
by apply: eq_sum=>i; rewrite /= approximant_collapse.
Qed.

Lemma approximant_expect_step Q c mu k : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  expect Q (@approximant P rho0 k.+1 c) =
  family_observe mu (fun d => expect Q (@approximant P rho0 k d)).
Proof.
move=>Hs Hr Ho.
rewrite (@approximant_global_step c mu k Hs Hr Ho) CQMixtureExpectation.expect_mix.
by apply: eq_sum=>i; rewrite probability_distributionE.
Qed.

Theorem horizon_pre_observe k Q c : c.2 \is den1lf -> configuration_owned p c ->
  @observe P (@horizon_pre P k Q) c = expect Q (@approximant P rho0 k c).
Proof.
elim: k c=>[|k IH] [[pc [m|]] rho] Hr Ho.
- exact: terminal_pre_observe (den1lf_den Hr).
- by rewrite /observe /= CQHoare.expect_bottom.
- change (\Tr (@horizon_pre P k.+1 Q pc m \o rho) =
    expect Q (@approximant P rho0 k.+1 (global_config pc (Some m) rho))).
  rewrite /horizon_pre -/(@horizon_pre P k Q).
  case Ed: (@selected_descriptor P pc m)=>[d|].
  + have [a [Hd Hwf]] := @selected_descriptor_some P pc m d Ed.
    have Hs := labeled_step_erasure (@descriptor_step n p pc m rho a d Hd Hwf).
    rewrite (@descriptor_pre_observe P (@horizon_pre P k Q) d pc m rho Hr) (@approximant_expect_step Q _ _ k Hs Hr Ho).
    apply: eq_sum=>i; congr (_ * _).
    apply: IH; first exact: global_step_normalized Hs Hr i.
    exact: (@global_step_owned n p _ _ (@processes_wf P) Ho Hs i).
  + rewrite (@approximant_terminal P rho0 _ (@descriptor_terminal P pc m rho Ho Ed)).
    exact: terminal_pre_observe (den1lf_den Hr).
- rewrite (@approximant_terminal P rho0 _ (@failure_terminal n p pc rho)).
  by rewrite /observe /= CQHoare.expect_bottom.
Qed.

End Horizon.
End DistributedHorizonExpectation.


Module DistributedNetworkValidity.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedSchedulerResults DistributedCorrespondence CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition run := DistributedCQInput.run.

Theorem run_translate (S : program) rho :
  run S rho = CQHoare.run (successful_sequentialize (processes S)) rho.
Proof.
apply: DistributedCQInput.run_kernel=>m r out.
exact: denote_program_point.
Qed.

Definition valid total (P : assertion) (S : program) Q :=
  forall rho : @CQState.state cmem Hq,
  if total then expect P rho <= expect Q (run S rho)
  else expect (complement Q) (run S rho) <= expect (complement P) rho.

Definition normalized_valid total (P : assertion) (S : program) Q :=
  forall m (rho : 'FD1(Hq)),
  if total then expect P (CQState.point m (rho : 'FD(Hq))) <= expect Q (denote_program S m rho)
  else expect (complement Q) (denote_program S m rho) <=
    expect (complement P) (CQState.point m (rho : 'FD(Hq))).

Theorem valid_translate_iff total P (S : program) Q :
  valid total P S Q <-> CQHoare.valid total P (successful_sequentialize (processes S)) Q.
Proof.
split=>H rho; have Hs := H rho.
- by rewrite run_translate in Hs.
- by rewrite run_translate.
Qed.

Theorem valid_normalized_iff total P (S : program) Q :
  valid total P S Q <-> normalized_valid total P S Q.
Proof.
rewrite valid_translate_iff DistributedNormalizedTests.valid_normalized_iff.
split=>H m rho; have Hpoint := H m rho.
- by rewrite denote_program_sequentialize.
- by rewrite denote_program_sequentialize in Hpoint.
Qed.

Lemma valid_total_partial P S Q : valid true P S Q -> valid false P S Q.
Proof.
move=>H; apply/(proj2 (valid_translate_iff _ _ _ _)).
apply: CQHoare.valid_total_partial; exact: (proj1 (valid_translate_iff _ _ _ _) H).
Qed.

Lemma valid_consequence total P Q P' Q' S :
  semantic_le P' P -> semantic_le Q Q' -> valid total P S Q -> valid total P' S Q'.
Proof.
move=>HP HQ H; apply/(proj2 (valid_translate_iff _ _ _ _)).
apply: CQHoare.valid_consequence HP HQ _.
exact: (proj1 (valid_translate_iff _ _ _ _) H).
Qed.

Theorem derives_sound total P (S : program) Q :
  DistributedNetworkRules.derives total P (processes S) Q -> valid total P S Q.
Proof.
move=>D; apply/(proj2 (valid_translate_iff _ _ _ _)).
exact: DistributedNetworkRules.derives_translate_sound D.
Qed.

Theorem translated_derives_iff total P (S : program) Q :
  CQHoare.derives total P (successful_sequentialize (processes S)) Q <-> valid total P S Q.
Proof. rewrite valid_translate_iff; exact: CQHoare.sound_complete. Qed.
End DistributedNetworkValidity.


Module DistributedHorizonRemainder.
(* Finite operational horizons as effects; see the D5 completeness argument. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate DistributedHorizonExpectation DistributedObservables CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation C := hermitian.C.

Lemma expect_state_mono (I : choiceType) (H : chsType) (Q : I -> 'FO(H))
    (d e : @CQState.state I H) : d ⊑ e -> expect Q d <= expect Q e.
Proof.
move=>/levdP Hde; rewrite /expect /sum; apply: ler_etlim.
- exact: (summable_cvg (f := Summable.build (expect_summable Q d))).
- exact: (summable_cvg (f := Summable.build (expect_summable Q e))).
- move=>J; rewrite /psum; apply: ler_sum=>i _.
  rewrite /expect_term ![\Tr (Q _ \o _)]lftraceC.
  move: (Hde (val i))=>/lef_psdtr Htrace; apply: Htrace; exact: is_psdlf.
Qed.

Section Remainder.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Variable Q : assertion.
Local Notation V := (@value P rho0).
Local Notation A := (@approximant P rho0).

Definition remainder k c := expect Q (V c) - expect Q (A k c).

Lemma value_global_step c mu (Hs : global_step p c mu)
    (Hr : c.2 \is den1lf) : configuration_owned p c ->
  V c = CQStateMixture.mix (probability_distribution (global_step_probability Hs Hr))
    (fun i => V (branch_value mu i)).
Proof.
move=>Ho; apply/vdistrP=>out; rewrite CQStateMixture.mixE.
have Hp := @ProjectedGlobal P rho0 c mu (conj Hr Ho) Hs.
apply: (eq_trans (@value_bellman P rho0 c _ out Hp)).
by apply: eq_sum=>i; rewrite /= value_collapse.
Qed.

Lemma value_expect_step c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  expect Q (V c) = family_observe mu (fun d => expect Q (V d)).
Proof.
move=>Hs Hr Ho; rewrite (@value_global_step c mu Hs Hr Ho) CQMixtureExpectation.expect_mix.
by apply: eq_sum=>i; rewrite probability_distributionE.
Qed.

Lemma approximant_expect_le k c : expect Q (A k c) <= expect Q (V c).
Proof.
apply: expect_state_mono.
exact: (@CQState.chain_sup_upper cmem Hq (fun j => A j c) (@approximant_increasing P rho0 c) k).
Qed.

Lemma remainder_ge0 k c : 0 <= remainder k c.
Proof. rewrite /remainder subr_ge0; exact: approximant_expect_le. Qed.

Lemma remainder_le1 k c : remainder k c <= 1.
Proof.
apply: (le_trans _ (expect_le1 Q (V c))).
by rewrite /remainder lerBlDr lerDl; exact: expect_ge0.
Qed.

Lemma remainder_bound k c : `|remainder k c| <= 1.
Proof. rewrite ger0_norm ?remainder_ge0 //; exact: remainder_le1. Qed.

Lemma remainder_decreasing k c : remainder k.+1 c <= remainder k c.
Proof.
rewrite /remainder lerD2l lerN2; apply: expect_state_mono.
exact: (@approximant_increasing P rho0 c k k.+1 (leqnSn k)).
Qed.

Lemma remainder_cvg c : remainder k c @[k --> \oo] --> 0.
Proof.
have C := @CQExpectation.expect_chain_sup cmem Hq Q (fun k => A k c)
  (@approximant_increasing P rho0 c).
change ((fun k => expect Q (A k c)) @ \oo --> expect Q (V c))%classic in C.
have D := cvgB (cvg_cst (expect Q (V c))) C.
rewrite subrr in D; exact: D.
Qed.

Lemma remainder_step k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (remainder k) = remainder k.+1 c.
Proof.
move=>Hs Hr Ho.
have Hmu := global_step_probability Hs Hr.
have HV d : `|expect Q (V d)| <= 1 by rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
have HA d : `|expect Q (A k d)| <= 1 by rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
have SV := observe_summable Hmu (ler01 : (0 : C) <= 1) HV.
have SA := observe_summable Hmu (ler01 : (0 : C) <= 1) HA.
change (family_observe mu (fun d => expect Q (V d) - expect Q (A k d)) =
  expect Q (V c) - expect Q (A k.+1 c)).
apply: (eq_trans _ (f_equal2 (fun x y : C => x-y)
  (esym (@value_expect_step c mu Hs Hr Ho))
  (esym (@approximant_expect_step P rho0 Q c mu k Hs Hr Ho)))).
rewrite /family_observe.
rewrite -(summable_sumB (Summable.build SV) (Summable.build SA)).
by apply: eq_sum=>i; rewrite /= mulrBr.
Qed.

Lemma remainder_superharmonic k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (remainder k) <= remainder k c.
Proof. move=>Hs Hr Ho; rewrite (remainder_step k Hs Hr Ho); exact: remainder_decreasing. Qed.


Definition progress_potential k c :=
  if k is j.+1 then remainder j c else expect Q (V c).

Lemma progress_nonnegative k c : 0 <= progress_potential k c.
Proof. case: k=>[|k] /=; [exact: expect_ge0 | exact: remainder_ge0]. Qed.
Lemma progress_bound k c : `|progress_potential k c| <= 1.
Proof.
case: k=>[|k] /=; last exact: remainder_bound.
rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
Qed.
Lemma progress_decreasing k c : progress_potential k.+1 c <= progress_potential k c.
Proof.
case: k=>[|k] /=; last exact: remainder_decreasing.
by rewrite /remainder lerBlDr lerDl; exact: expect_ge0.
Qed.
Lemma progress_step k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (progress_potential k) = progress_potential k.+1 c.
Proof.
move=>Hs Hr Ho; case: k=>[|k]; last exact: remainder_step Hs Hr Ho.
change (family_observe mu (fun d => expect Q (V d)) = remainder 0 c).
have Ezero : successful_component c = CQState.bottom.
  case: (successful_component_terminal_or_zero p c)=>[Ht|Hz] //.
  exfalso; exact: Ht mu Hs.
rewrite /remainder /approximant Ezero CQHoare.expect_bottom subr0.
symmetry; exact: value_expect_step Hs Hr Ho.
Qed.
Lemma progress_superharmonic k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (progress_potential k) <= progress_potential k c.
Proof.
move=>Hs Hr Ho; rewrite (progress_step k Hs Hr Ho); exact: progress_decreasing.
Qed.

End Remainder.
End DistributedHorizonRemainder.


Module DistributedSerialHoare.
(* Lemma C.9 for the raw serializer; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules CQAssertion CQPredicate CQHoare.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma pre_unroll_post_agree total b c (Q R : assertion) :
  (forall m, ~~ eval b m -> Q m = R m) ->
  forall k, pre total (CL.unroll b c k) Q = pre total (CL.unroll b c k) R.
Proof.
move=>H; elim=>[|k IH].
- by case: total; rewrite /pre /= /xp ?wp_abort ?wlp_abort.
- rewrite !pre_unrollS IH; apply/funext=>m; rewrite /conditional -/(eval b m).
  case E: (eval b m)=>//; apply: H; by rewrite E.
Qed.

Lemma pre_while_post_agree total b c (Q R : assertion) :
  (forall m, ~~ eval b m -> Q m = R m) ->
  pre total (CL.While b c) Q = pre total (CL.While b c) R.
Proof.
move=>H; apply/funext=>m; apply/val_inj.
change ((pre total (CL.While b c) Q m : 'End(Hq)) =
  (pre total (CL.While b c) R m : 'End(Hq))).
have CQ : ((fun k => (pre total (CL.unroll b c k) Q m : 'End(Hq))) @ \oo -->
    (pre total (CL.While b c) Q m : 'End(Hq)))%classic.
  by case: total; [exact: wp_unroll_cvg | exact: wlp_unroll_cvg].
have CR : ((fun k => (pre total (CL.unroll b c k) R m : 'End(Hq))) @ \oo -->
    (pre total (CL.While b c) R m : 'End(Hq)))%classic.
  by case: total in CQ *; [exact: wp_unroll_cvg | exact: wlp_unroll_cvg].
have EQ k := pre_unroll_post_agree total c H k.
have Eseq : (fun k => (pre total (CL.unroll b c k) Q m : 'End(Hq))) =
    (fun k => (pre total (CL.unroll b c k) R m : 'End(Hq))).
  by apply/funext=>k; rewrite EQ.
rewrite Eseq in CQ.
by rewrite -(cvg_lim (@norm_hausdorff _ _) CQ) (cvg_lim (@norm_hausdorff _ _) CR).
Qed.

Definition partial_serial_post n (p : 'I_n -> process) (Q : assertion) :=
  conditional (DistributedLanguage.term p) Q (mask (blocked p) semantic_top).

Lemma partial_serial_postE n (p : 'I_n -> process) Q m :
  (partial_serial_post p Q m : 'End(Hq)) =
  (mask (DistributedLanguage.term p) Q m : 'End(Hq)) +
  (mask (fun s => ~~ DistributedLanguage.term p s && blocked p s) semantic_top m : 'End(Hq)).
Proof.
rewrite /partial_serial_post /conditional /mask.
by case: (DistributedLanguage.term p m); case: (blocked p m); rewrite /= ?addr0 ?add0r.
Qed.

Lemma final_test_total_pre n (p : 'I_n -> process) Q :
  pre true (CL.Conditional (termination_guard p) CL.Skip CL.Abort)
    (mask (DistributedLanguage.term p) Q) = mask (DistributedLanguage.term p) Q.
Proof.
rewrite pre_conditional /pre /= /xp wp_skip wp_abort.
apply/funext=>m; rewrite /conditional /mask -/(eval (termination_guard p) m) eval_termination_guard.
by case: (DistributedLanguage.term p m).
Qed.

Lemma final_test_partial_pre n (p : 'I_n -> process) Q :
  pre false (CL.Conditional (termination_guard p) CL.Skip CL.Abort)
    (mask (DistributedLanguage.term p) Q) =
  conditional (DistributedLanguage.term p) Q semantic_top.
Proof.
rewrite pre_conditional /pre /= /xp wlp_skip wlp_abort.
apply/funext=>m; rewrite /conditional /mask -/(eval (termination_guard p) m) eval_termination_guard.
by case: (DistributedLanguage.term p m).
Qed.

Lemma raw_partial_post_agree n (p : 'I_n -> process) Q :
  pre false (sequentialize p) (conditional (DistributedLanguage.term p) Q semantic_top) =
  pre false (sequentialize p) (partial_serial_post p Q).
Proof.
rewrite /sequentialize !pre_sequence.
congr (pre false _ _); apply: pre_while_post_agree=>m Hblocked.
have Hb : blocked p m := Hblocked.
rewrite /partial_serial_post /conditional /mask Hb.
by case: (DistributedLanguage.term p m).
Qed.

Theorem total_raw_sequentialization_iff (P Q : assertion) (S : program) :
  DistributedNetworkValidity.valid true P S (mask (DistributedLanguage.term (processes S)) Q) <->
  CQHoare.valid true P (sequentialize (processes S))
    (mask (DistributedLanguage.term (processes S)) Q).
Proof.
rewrite DistributedNetworkValidity.valid_translate_iff !valid_iff.
by rewrite /successful_sequentialize pre_sequence final_test_total_pre.
Qed.

Theorem partial_raw_sequentialization_iff (P Q : assertion) (S : program) :
  DistributedNetworkValidity.valid false P S (mask (DistributedLanguage.term (processes S)) Q) <->
  CQHoare.valid false P (sequentialize (processes S)) (partial_serial_post (processes S) Q).
Proof.
rewrite DistributedNetworkValidity.valid_translate_iff !valid_iff.
by rewrite /successful_sequentialize pre_sequence final_test_partial_pre raw_partial_post_agree.
Qed.
End DistributedSerialHoare.


Module DistributedPartialCompleteness.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules DistributedNetworkPre DistributedResidualSemantics DistributedAllRendezvous CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem derives_pre_partial (S : program) (Q : assertion) :
  derives false (CQHoare.pre false (successful_sequentialize (processes S)) Q) (processes S) Q.
Proof.
pose I := CQHoare.pre false (network_tail (processes S)) Q.
apply: (@DNetworkConsequence false
  (CQHoare.pre false (successful_sequentialize (processes S)) Q)
  (mask (DistributedLanguage.term (processes S)) I)
  (CQHoare.pre false (successful_sequentialize (processes S)) Q) Q
  (process_count S) (processes S)).
- exact: semantic_le_refl.
- exact: tail_pre_post.
- apply: DDistributedPartial.
  + apply: CQHoare.derives_complete.
    apply/(proj2 (CQHoare.valid_iff _ _ _ _)).
    rewrite initialization_pre; exact: semantic_le_refl.
  + have H := @all_tail_invariants S false Q.
    elim: H=>[|bc bs Hb Hbs IH]; constructor=>//.
    exact: CQHoare.derives_complete Hb.
Qed.

Theorem derives_complete_partial (P Q : assertion) (S : program) :
  DistributedNetworkValidity.valid false P S Q -> derives false P (processes S) Q.
Proof.
move=>H.
have Htranslated := proj1 (DistributedNetworkValidity.valid_translate_iff false P S Q) H.
have Hpre := proj1 (CQHoare.valid_iff false P (successful_sequentialize (processes S)) Q) Htranslated.
apply: (@DNetworkConsequence false
  (CQHoare.pre false (successful_sequentialize (processes S)) Q) Q P Q
  (process_count S) (processes S) Hpre (semantic_le_refl Q)).
exact: derives_pre_partial.
Qed.

Theorem partial_sound_complete (P Q : assertion) (S : program) :
  derives false P (processes S) Q <-> DistributedNetworkValidity.valid false P S Q.
Proof. split; [exact: DistributedNetworkValidity.derives_sound | exact: derives_complete_partial]. Qed.
End DistributedPartialCompleteness.


Module DistributedHorizonEffects.
(* Finite operational horizons as effects; see the D5 completeness argument. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate DistributedHorizonExpectation DistributedHorizonRemainder DistributedObservables DistributedSerialScheduler DistributedSerialInvariant DistributedResidualSemantics DistributedCorrespondence DistributedAllRendezvous DistributedNormalizedTests CQAssertion CQPredicate CQExpectationLimits.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Effects.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable Q : assertion.

Definition tail_assertion := wp (ClassicalSemantics.denote (network_tail p)) Q.
Definition horizon_assertion k := @horizon_pre P k Q (fun i => idle_control (p i)).

Lemma idle_value_expect rho0 m rho : rho0 \is den1lf -> rho \is den1lf ->
  expect Q (@value P rho0 (idle_configuration p m rho)) =
  \Tr (tail_assertion m \o rho).
Proof.
move=>Hr0 Hr.
have Hinv := @idle_serial_invariant P m rho Hr.
rewrite -(@residual_value P rho0 Hr0 _ Hinv) /residual_state /=.
case: asboolP=>[Hd|Hd]; last by exfalso; apply: Hd; exact: den1lf_den Hr.
rewrite (residual_idle p (idle_ready p)) -expect_wp CQExpectation.expect_point.
by [].
Qed.

Lemma horizon_assertion_pairing rho0 k m rho : rho \is den1lf ->
  \Tr (horizon_assertion k m \o rho) =
  expect Q (@approximant P rho0 k (idle_configuration p m rho)).
Proof.
move=>Hr; exact: (@horizon_pre_observe P rho0 k Q (idle_configuration p m rho)
  Hr (idle_owned p m rho)).
Qed.

Lemma horizon_assertion_mono : semantic_chain horizon_assertion.
Proof.
move=>k m; apply: operator_le_normalized=>rho.
rewrite !(@horizon_assertion_pairing rho _ m rho (is_den1lf rho)).
apply: expect_state_mono.
exact: (@approximant_increasing P rho (idle_configuration p m rho) k k.+1 (leqnSn k)).
Qed.

Lemma horizon_assertion_bound k : semantic_le (horizon_assertion k) tail_assertion.
Proof.
move=>m; apply: operator_le_normalized=>rho.
rewrite (@horizon_assertion_pairing rho k m rho (is_den1lf rho))
  -(@idle_value_expect rho m rho (is_den1lf rho) (is_den1lf rho)).
exact: approximant_expect_le.
Qed.

Lemma horizon_assertion_sup : semantic_sup horizon_assertion = tail_assertion.
Proof.
apply/funext=>m.
have E (rho : 'FD1(Hq)) :
  \Tr (semantic_sup horizon_assertion m \o rho) = \Tr (tail_assertion m \o rho).
  have C1 := @expect_semantic_sup cmem Hq horizon_assertion
    (CQState.point m (rho : 'FD(Hq))) horizon_assertion_mono.
  have C2 := @CQExpectation.expect_chain_sup cmem Hq Q
    (fun k => @approximant P rho k (idle_configuration p m rho))
    (@approximant_increasing P rho (idle_configuration p m rho)).
  have E1 : (fun k => expect (horizon_assertion k) (CQState.point m (rho : 'FD(Hq)))) =
    (fun k => expect Q (@approximant P rho k (idle_configuration p m rho))).
    apply/funext=>k; rewrite CQExpectation.expect_point.
    exact: (@horizon_assertion_pairing rho k m rho (is_den1lf rho)).
  rewrite E1 CQExpectation.expect_point in C1.
  change ((fun k => expect Q (@approximant P rho k (idle_configuration p m rho))) @ \oo -->
    expect Q (@value P rho (idle_configuration p m rho)))%classic in C2.
  rewrite (@idle_value_expect rho m rho (is_den1lf rho) (is_den1lf rho)) in C2.
  exact: (eq_trans (esym (cvg_lim (@norm_hausdorff _ _) C1))
    (cvg_lim (@norm_hausdorff _ _) C2)).
apply/val_inj/eqP; rewrite eq_le; apply/andP; split;
  apply: operator_le_normalized=>rho; by rewrite E.
Qed.

Lemma horizon_assertion_cvg m :
  (horizon_assertion k m : 'End(Hq)) @[k --> \oo] --> (tail_assertion m : 'End(Hq)).
Proof.
rewrite -horizon_assertion_sup.
exact: (@semantic_sup_cvg cmem Hq horizon_assertion horizon_assertion_mono m).
Qed.

Lemma remainder_effect k m :
  ((tail_assertion m : 'End(Hq)) - (horizon_assertion k m : 'End(Hq))) \is obslf.
Proof.
apply/obslf_lefP; split.
- rewrite subv_ge0; exact: horizon_assertion_bound.
- apply: (le_trans (y := (tail_assertion m : 'End(Hq)))); last exact: obsf_le1.
  by rewrite levBlDr levDl; exact: obsf_ge0.
Qed.

Definition remainder_assertion k m : 'FO(Hq) := ObsLf_Build (remainder_effect k m).
Definition rank_assertion k := if k is j.+1 then remainder_assertion j else tail_assertion.

Lemma remainder_assertionE k m : (remainder_assertion k m : 'End(Hq)) =
  (tail_assertion m : 'End(Hq)) - (horizon_assertion k m : 'End(Hq)).
Proof. by []. Qed.

Lemma rank_assertion_decreasing k : semantic_le (rank_assertion k.+1) (rank_assertion k).
Proof.
case: k=>[|k] m.
- rewrite /rank_assertion remainder_assertionE levBlDr levDl; exact: obsf_ge0.
- rewrite /rank_assertion !remainder_assertionE levD2l levN2.
  exact: horizon_assertion_mono k m.
Qed.

Lemma rank_assertion_zero m :
  (rank_assertion k m : 'End(Hq)) @[k --> \oo] --> 0.
Proof.
rewrite -(@cvg_shiftS _ (fun k => (rank_assertion k m : 'End(Hq))) (nbhs 0)).
change ((fun k => (tail_assertion m : 'End(Hq)) -
  (horizon_assertion k m : 'End(Hq))) @ \oo --> 0)%classic.
have C := cvgB (cvg_cst (tail_assertion m : 'End(Hq))) (@horizon_assertion_cvg m).
rewrite subrr in C; exact: C.
Qed.

Lemma remainder_assertion_pairing rho0 k m rho : rho0 \is den1lf -> rho \is den1lf ->
  \Tr (remainder_assertion k m \o rho) =
  @remainder P rho0 Q k (idle_configuration p m rho).
Proof.
move=>Hr0 Hr; rewrite remainder_assertionE linearBl /= linearB /= /remainder
  (@idle_value_expect rho0 m rho Hr0 Hr) (@horizon_assertion_pairing rho0 k m rho Hr).
by [].
Qed.

Lemma rank_assertion_pairing rho0 k m rho : rho0 \is den1lf -> rho \is den1lf ->
  \Tr (rank_assertion k m \o rho) =
  @progress_potential P rho0 Q k (idle_configuration p m rho).
Proof.
move=>Hr0 Hr; case: k=>[|k].
- rewrite /rank_assertion /progress_potential.
  exact: esym (@idle_value_expect rho0 m rho Hr0 Hr).
- exact: (@remainder_assertion_pairing rho0 k m rho Hr0 Hr).
Qed.

End Effects.
End DistributedHorizonEffects.


Module DistributedNetworkRanking.
(* Finite operational horizons as effects; see the D5 completeness argument. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedOperational DistributedDistribution DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate DistributedHorizonExpectation DistributedHorizonRemainder DistributedHorizonEffects DistributedObservables DistributedSerialScheduler DistributedSerialInvariant DistributedResidualSemantics DistributedCorrespondence DistributedAllRendezvous DistributedNormalizedTests DistributedRankingControls DistributedActiveStopping DistributedActiveLower DistributedNetworkRules CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Ranking.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable Q : assertion.
Local Notation ranks := (@rank_assertion P Q).

Lemma active_pair_rank rho0 k (i j : 'I_n) s t m rho : rho0 \is den1lf ->
  (i < j)%N ->
  serial_invariant P (global_config
    (replace (replace (fun z => idle_control (p z)) i (Executing s)) j (Executing t))
    (Some m) rho) ->
  \Tr (wp (ClassicalSemantics.denote (CL.Sequence (translate_statement s) (translate_statement t)))
    (ranks k) m \o rho) <=
  @progress_potential P rho0 Q k (global_config
    (replace (replace (fun z => idle_control (p z)) i (Executing s)) j (Executing t))
    (Some m) rho).
Proof.
move=>Hr0 Hij Hinv.
pose pc := replace (replace (fun z => idle_control (p z)) i (Executing s)) j (Executing t).
have Hp : ready (fun z => idle_control (p z)) := DistributedSerialScheduler.idle_ready p.
have Eactive : ClassicalSemantics.denote (active_program (enum 'I_n) pc CL.Skip) =
  ClassicalSemantics.denote (CL.Sequence (translate_statement s) (translate_statement t)).
  rewrite /pc (@active_program_pair n (fun z => idle_control (p z)) i j s t CL.Skip Hp Hij).
  change (slet (ClassicalSemantics.denote (translate_statement s))
    (ClassicalSemantics.denote (CL.Sequence (translate_statement t) CL.Skip)) =
    slet (ClassicalSemantics.denote (translate_statement s)) (ClassicalSemantics.denote (translate_statement t))).
  by rewrite ClassicalSemantics.denote_skip_right.
rewrite -Eactive.
apply: (@active_program_stopping P (@progress_potential P rho0 Q k)
  _ _ _ (enum 'I_n) (enum_uniq _) pc CL.Skip (ranks k) _ m rho Hinv).
- move=>c _; exact: progress_nonnegative.
- move=>c _; exact: progress_bound.
- move=>c mu [[Hr Ho] _] Hs; exact: progress_superharmonic Hs Hr Ho.
- move=>u r Hend; rewrite /pc finish_active_pair in Hend *.
  rewrite wp_skip.
  rewrite (@rank_assertion_pairing P Q rho0 k u r Hr0 (proj1 (proj1 Hend))).
  by [].
Qed.

Theorem enabled_rank_bound k (a : rendezvous_index p) g c :
  index_command a = Some (g,c) ->
  semantic_le (mask (eval g) (CQHoare.wp_command c (ranks k))) (ranks k.+1).
Proof.
move=>Ha m; rewrite /mask; case Hg: (eval g m); last exact: obsf_ge0.
apply: operator_le_normalized=>rho.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
  by case: Hmatch=>t ch x e; exists t, x, e.
case: Hass=>t [x [e He]]; subst effect.
pose pc := fun z => idle_control (p z).
pose src := global_config pc (Some m) (rho : 'End(Hq)).
pose dst := global_config
  (replace (replace pc (first_process a)
    (Executing (process_body (p (first_process a)) (first_branch a))))
    (second_process a) (Executing (process_body (p (second_process a)) (second_branch a))))
  (Some (m.[x <- eval e m])%M) (rho : 'End(Hq)).
have Hinv : serial_invariant P src := @idle_serial_invariant P m rho (is_den1lf rho).
have Hi : pc (first_process a) = Waiting :=
  @idle_control_waiting (p (first_process a)) (first_branch a).
have Hk : pc (second_process a) = Waiting :=
  @idle_control_waiting (p (second_process a)) (second_branch a).
have Hstep : global_step p src (certain dst).
  exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
have Hdst : serial_invariant P dst := serial_global_step Hinv Hstep tt.
have EB := @active_pair_rank rho k (first_process a) (second_process a)
  (process_body (p (first_process a)) (first_branch a))
  (process_body (p (second_process a)) (second_branch a))
  (m.[x <- eval e m])%M rho (is_den1lf rho) Hik Hdst.
have EP := @progress_step P rho Q k src (certain dst) Hstep
  (is_den1lf rho) (proj2 (proj1 Hinv)).
rewrite observe_certain in EP.
have ER := @rank_assertion_pairing P Q rho k.+1 m rho (is_den1lf rho) (is_den1lf rho).
change (\Tr (CQHoare.pre true c (ranks k) m \o rho) <= \Tr (ranks k.+1 m \o rho)).
rewrite HE CQHoare.pre_sequence /CQHoare.pre CQPrimitive.assign_pre.
apply: (le_trans EB).
by rewrite EP -ER.
Qed.

Theorem tail_network_ranking : network_ranking (@tail_assertion P Q) p.
Proof.
apply: (ListRanking (list_rank := ranks)).
- exact: rank_assertion_decreasing.
- exact: semantic_le_refl.
- exact: rank_assertion_zero.
- move=>k; rewrite -rendezvous_indicesE.
  elim: (rendezvous_indices p)=>[|a rest IH] /=; first exact: List.Forall_nil.
  case Ha: (index_command a)=>[[g c]|] /=; last exact: IH.
  apply: List.Forall_cons; last exact: IH.
  exact: enabled_rank_bound Ha.
Qed.

End Ranking.
End DistributedNetworkRanking.


Module DistributedTotalCompleteness.
(* Relative completeness of the independent distributed inference rules. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules DistributedNetworkPre DistributedResidualSemantics DistributedAllRendezvous DistributedHorizonEffects DistributedNetworkRanking CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem derives_pre_total (S : program) (Q : assertion) :
  derives true (CQHoare.pre true (successful_sequentialize (processes S)) Q) (processes S) Q.
Proof.
pose I := CQHoare.pre true (network_tail (processes S)) Q.
apply: (@DNetworkConsequence true
  (CQHoare.pre true (successful_sequentialize (processes S)) Q)
  (mask (DistributedLanguage.term (processes S)) I)
  (CQHoare.pre true (successful_sequentialize (processes S)) Q) Q
  (process_count S) (processes S)).
- exact: semantic_le_refl.
- exact: tail_pre_post.
- apply: DDistributedTotal.
  + apply: CQHoare.derives_complete.
    apply/(proj2 (CQHoare.valid_iff _ _ _ _)).
    rewrite initialization_pre; exact: semantic_le_refl.
  + have H := @all_tail_invariants S true Q.
    elim: H=>[|bc bs Hb Hbs IH]; constructor=>//.
    exact: CQHoare.derives_complete Hb.
  + exact: (@tail_network_ranking S Q).
  + exact: tail_pre_deadlock.
Qed.

Theorem derives_complete_total (P Q : assertion) (S : program) :
  DistributedNetworkValidity.valid true P S Q -> derives true P (processes S) Q.
Proof.
move=>H.
have Htranslated := proj1 (DistributedNetworkValidity.valid_translate_iff true P S Q) H.
have Hpre := proj1 (CQHoare.valid_iff true P (successful_sequentialize (processes S)) Q) Htranslated.
apply: (@DNetworkConsequence true
  (CQHoare.pre true (successful_sequentialize (processes S)) Q) Q P Q
  (process_count S) (processes S) Hpre (semantic_le_refl Q)).
exact: derives_pre_total.
Qed.

Theorem total_sound_complete (P Q : assertion) (S : program) :
  derives true P (processes S) Q <-> DistributedNetworkValidity.valid true P S Q.
Proof. split; [exact: DistributedNetworkValidity.derives_sound | exact: derives_complete_total]. Qed.

Theorem derives_pre total (S : program) (Q : assertion) :
  derives total (CQHoare.pre total (successful_sequentialize (processes S)) Q) (processes S) Q.
Proof.
case: total; [exact: derives_pre_total | exact: DistributedPartialCompleteness.derives_pre_partial].
Qed.

Theorem derives_complete total (P Q : assertion) (S : program) :
  DistributedNetworkValidity.valid total P S Q -> derives total P (processes S) Q.
Proof.
case: total; [exact: derives_complete_total | exact: DistributedPartialCompleteness.derives_complete_partial].
Qed.

Theorem sound_complete total (P Q : assertion) (S : program) :
  derives total P (processes S) Q <-> DistributedNetworkValidity.valid total P S Q.
Proof. split; [exact: DistributedNetworkValidity.derives_sound | exact: derives_complete]. Qed.
End DistributedTotalCompleteness.

(* Public API: one judgment for guarded statements and one for networks. *)
Module DistributedHoare.
Module Local.
Include DistributedGuardedRules.
Include DistributedLocalHoare.
End Local.
Module Network.
Include DistributedNetworkRules.
Include DistributedNetworkValidity.
Include DistributedTotalCompleteness.
End Network.
End DistributedHoare.
