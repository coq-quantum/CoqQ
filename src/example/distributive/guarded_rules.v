(* Independent guarded-command rules, quantum ranking assertions, and
   soundness/completeness for their shared-language translation. *)
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
From quantum.example.distributive Require Import language sequentialization.
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


Module DistributedGuardedRules.
Import DistributedLanguage DistributedSequentialization CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Implicit Types P Q R : assertion.

Lemma conditional_chain_none (bs : seq (expression bool * CL.command)) m :
  all (fun bc => ~~ eval bc.1 m) bs -> CL.denote (conditional_chain bs) m = abort_sem m.
Proof.
elim: bs=>[|[b c] bs IH] // /andP[Hb Hbs].
change (CL.denote (CL.Conditional b c (conditional_chain bs)) m = abort_sem m).
rewrite CL.denote_conditional (negbTE Hb); exact: IH.
Qed.

Lemma conditional_chain_selected n (g : 'I_n -> expression bool) (b : 'I_n -> CL.command)
    (indices : seq 'I_n) m i :
  exclusive g -> i \in indices -> eval (g i) m ->
  CL.denote (conditional_chain [seq (g j,b j) | j <- indices]) m = CL.denote (b i) m.
Proof.
move=>Hex; elim: indices=>[|j indices IH] //.
change (i \in j :: indices -> eval (g i) m ->
  CL.denote (CL.Conditional (g j) (b j) (conditional_chain [seq (g z,b z) | z <- indices])) m = CL.denote (b i) m).
rewrite inE=>/orP[/eqP E|Hi] Hgi.
- subst j; by rewrite CL.denote_conditional Hgi.
- rewrite CL.denote_conditional; case Hgj: (eval (g j) m).
  + by rewrite (Hex m j i Hgj Hgi).
  + exact: IH Hi Hgi.
Qed.

Lemma conditional_chain_bound total P Q (bs : seq (expression bool * CL.command)) m :
  List.Forall (fun bc : expression bool * CL.command => eval bc.1 m ->
    (P m : 'End(Hq)) ⊑ CQRules.pre total bc.2 Q m) bs ->
  (~~ has (fun bc => eval bc.1 m) bs ->
    (P m : 'End(Hq)) ⊑ CQRules.pre total CL.Abort Q m) ->
  (P m : 'End(Hq)) ⊑ CQRules.pre total (conditional_chain bs) Q m.
Proof.
elim: bs=>[|[b c] bs IH] /=.
- by move=>_ Hnone; apply: Hnone.
- move=>/List.Forall_cons_iff [Hhead Htail] Hnone.
  rewrite CQRules.pre_conditional /conditional /= -/(eval b m); case Eb: (eval b m).
  + exact: Hhead Eb.
  + apply: IH Htail _=>Hbs; apply: Hnone; by rewrite /= Eb Hbs.
Qed.

Lemma conditional_chain_valid total P Q (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command => CQHoare.valid total (mask (eval bc.1) P) bc.2 Q) bs ->
  (forall m, ~~ has (fun bc => eval bc.1 m) bs ->
    (P m : 'End(Hq)) ⊑ CQRules.pre total CL.Abort Q m) ->
  CQHoare.valid total P (conditional_chain bs) Q.
Proof.
move=>Hbranches Hnone; apply/(proj2 (CQRules.valid_iff _ _ _ _))=>m.
apply: conditional_chain_bound; last exact: Hnone.
elim: Hbranches=>[|[b c] rest Hvalid Htail IH]; constructor=>// Hb.
move: ((proj1 (CQRules.valid_iff _ _ _ _) Hvalid) m).
by rewrite /mask /= Hb.
Qed.

Lemma conditional_chain_upper total Q R
    (bs : seq (expression bool * CL.command)) m :
  List.Forall (fun bc : expression bool * CL.command => eval bc.1 m ->
    (CQRules.pre total bc.2 Q m : 'End(Hq)) ⊑ R m) bs ->
  has (fun bc => eval bc.1 m) bs ->
  (CQRules.pre total (conditional_chain bs) Q m : 'End(Hq)) ⊑ R m.
Proof.
elim: bs=>[|[b c] bs IH] //=.
move=>/List.Forall_cons_iff [Hhead Htail].
rewrite CQRules.pre_conditional /conditional /= -/(eval b m).
case Eb: (eval b m)=>/= Hany; first exact: Hhead Eb.
exact: IH Htail Hany.
Qed.

Definition loop_guard n (g : 'I_n -> expression bool) :=
  guards_any [seq g i | i <- enum 'I_n].
Definition enabled n (g : 'I_n -> expression bool) m :=
  has (fun i => eval (g i) m) (enum 'I_n).

Lemma eval_loop_guard n (g : 'I_n -> expression bool) m :
  eval (loop_guard g) m = enabled g m.
Proof. by rewrite /loop_guard eval_guards_any has_map. Qed.

Lemma enabledP n (g : 'I_n -> expression bool) m :
  reflect (exists i, eval (g i) m) (enabled g m).
Proof.
apply: (iffP hasP).
- by move=>[i _ Hi]; exists i.
- by move=>[i Hi]; exists i; rewrite ?mem_enum.
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
      (mask (eval (g i)) (CQRules.wp_command (translate_statement (b i)) (ranking_assertion k)))
      (ranking_assertion k.+1)
}.

Lemma ranking_transfer P n (g : 'I_n -> expression bool) b :
  ranking P g b ->
  CQRules.ranking P (loop_guard g)
    (conditional_chain [seq (g i,translate_statement (b i)) | i <- enum 'I_n]).
Proof.
move=>[r dec ini zero step]; apply: (CQRules.Ranking (ranking_assertion := r)).
- exact: dec.
- exact: ini.
- exact: zero.
move=>k m.
rewrite /mask -/(eval (loop_guard g) m) eval_loop_guard.
case E: (enabled g m); last exact: obsf_ge0.
change ((CQRules.pre true (conditional_chain
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
rewrite -E; apply: CQRules.valid_while_partial; rewrite E.
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
rewrite -E; apply: CQRules.valid_while_total.
- rewrite E; exact: guarded_chain_valid.
- exact: ranking_transfer Hr.
Qed.

Inductive derives : bool -> assertion -> statement -> assertion -> Prop :=
| DAtom total P a Q : CQRules.derives total P (translate_atom a) Q ->
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
- exact: CQRules.derives_sound.
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
  CQRules.pre total (conditional_chain [seq (g j,b j) | j <- indices]) Q m =
  CQRules.pre total (b i) Q m.
Proof.
move=>Hex; elim: indices=>[|j indices IH] //.
change (i \in j :: indices -> eval (g i) m ->
  CQRules.pre total (CL.Conditional (g j) (b j)
    (conditional_chain [seq (g z,b z) | z <- indices])) Q m =
  CQRules.pre total (b i) Q m).
rewrite inE=>/orP[/eqP E|Hi] Hgi.
- subst j; by rewrite CQRules.pre_conditional /conditional -/(eval (g i) m) Hgi.
- rewrite CQRules.pre_conditional /conditional -/(eval (g j) m).
  case Hgj: (eval (g j) m).
  + by rewrite (Hex m j i Hgj Hgi).
  + exact: IH Hi Hgi.
Qed.

Lemma conditional_chain_pre_none total Q
    (bs : seq (expression bool * CL.command)) m :
  ~~ has (fun bc => eval bc.1 m) bs ->
  CQRules.pre total (conditional_chain bs) Q m = CQRules.pre total CL.Abort Q m.
Proof.
elim: bs=>[|[b c] bs IH] //=.
rewrite negb_or=>/andP[Hb Hbs].
change (CQRules.pre total (CL.Conditional b c (conditional_chain bs)) Q m =
  CQRules.pre total CL.Abort Q m).
rewrite CQRules.pre_conditional /conditional -/(eval b m) (negbTE Hb).
exact: IH Hbs.
Qed.

Lemma alternative_pre_branch total Q n (g : 'I_n -> expression bool) b i :
  exclusive g ->
  semantic_le (mask (eval (g i))
    (CQRules.pre total (conditional_chain [seq (g j,b j) | j <- enum 'I_n]) Q))
    (CQRules.pre total (b i) Q).
Proof.
move=>Hex m; rewrite /mask; case Ei: (eval (g i) m); last exact: obsf_ge0.
have Hi : i \in enum 'I_n by rewrite mem_enum.
by rewrite (@conditional_chain_pre_selected total Q n g b (enum 'I_n) m i Hex Hi Ei).
Qed.

Lemma alternative_pre_covered Q n (g : 'I_n -> expression bool) b :
  semantic_le (CQRules.pre true
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
    (CQRules.pre total (translate_statement (Repetition g b)) Q))
    (CQRules.pre total (translate_statement (b i))
      (CQRules.pre total (translate_statement (Repetition g b)) Q)).
Proof.
move=>Hex m; rewrite /mask; case Ei: (eval (g i) m); last exact: obsf_ge0.
have Eg : enabled g m by apply/enabledP; exists i.
have W := congr1 (fun A : assertion => A m)
  (CQRules.pre_while_unfold total (loop_guard g)
    (conditional_chain [seq (g j,translate_statement (b j)) | j <- enum 'I_n]) Q).
rewrite /conditional -/(eval (loop_guard g) m) eval_loop_guard Eg in W.
change ((CQRules.pre total (CL.While (loop_guard g)
  (conditional_chain [seq (g j,translate_statement (b j)) | j <- enum 'I_n])) Q m : 'End(Hq)) ⊑
  CQRules.pre total (translate_statement (b i))
    (CQRules.pre total (translate_statement (Repetition g b)) Q) m).
rewrite W.
have Hi : i \in enum 'I_n by rewrite mem_enum.
by rewrite (@conditional_chain_pre_selected total
  (CQRules.pre total (translate_statement (Repetition g b)) Q) n g
  (fun j => translate_statement (b j)) (enum 'I_n) m i Hex Hi Ei).
Qed.

Lemma loop_pre_post total Q n (g : 'I_n -> expression bool) b :
  semantic_le (mask (predC (enabled g))
    (CQRules.pre total (translate_statement (Repetition g b)) Q)) Q.
Proof.
have E : esem (loop_guard g) = enabled g.
  by apply/funext=>m; exact: eval_loop_guard.
rewrite -E; exact: CQRules.loop_invariant_post.
Qed.

Lemma loop_pre_ranking Q n (g : 'I_n -> expression bool) b : exclusive g ->
  ranking (CQRules.pre true (translate_statement (Repetition g b)) Q) g b.
Proof.
move=>Hex.
have [r dec ini zero step] := CQRules.loop_ranking (loop_guard g)
  (conditional_chain [seq (g i,translate_statement (b i)) | i <- enum 'I_n]) Q.
apply: (Ranking (ranking_assertion := r)).
- exact: dec.
- exact: ini.
- exact: zero.
move=>k i m; rewrite /mask; case Ei: (eval (g i) m); last exact: obsf_ge0.
have Eg : enabled g m by apply/enabledP; exists i.
have S := step k m.
rewrite /mask -/(eval (loop_guard g) m) eval_loop_guard Eg in S.
change (is_true ((CQRules.pre true (conditional_chain
  [seq (g j,translate_statement (b j)) | j <- enum 'I_n]) (r k) m : 'End(Hq)) ⊑ r k.+1 m)) in S.
have Hi : i \in enum 'I_n by rewrite mem_enum.
by rewrite (@conditional_chain_pre_selected true (r k) n g
  (fun j => translate_statement (b j)) (enum 'I_n) m i Hex Hi Ei) in S.
Qed.

Theorem derives_pre total s : statement_wf s -> forall Q,
  derives total (CQRules.pre total (translate_statement s) Q) s Q.
Proof.
elim: s=>[|a|s IHs t IHt|n g b IH|n g b IH] //=.
- move=>_ Q; apply: DAtom; exact: CQRules.derives_pre.
- move=>[Hs Ht] Q; rewrite CQRules.pre_sequence.
  apply: DSequence; [exact: IHs | exact: IHt].
- move=>[Hex Hwf] Q.
  have branches i : derives total
      (mask (eval (g i)) (CQRules.pre total
        (conditional_chain [seq (g j,translate_statement (b j)) | j <- enum 'I_n]) Q))
      (b i) Q.
    apply: (@DConsequence total (CQRules.pre total (translate_statement (b i)) Q) Q
      _ Q (b i)).
    + exact: alternative_pre_branch Hex.
    + exact: semantic_le_refl.
    + exact: IH.
  case E: total in branches *.
  + apply: DAlternativeTotal; [exact: Hex | exact: alternative_pre_covered | exact: branches].
  + apply: DAlternativePartial; [exact: Hex | exact: branches].
- move=>[Hex Hwf] Q.
  pose I := CQRules.pre total (translate_statement (Repetition g b)) Q.
  apply: (@DConsequence total I (mask (predC (enabled g)) I) I Q (Repetition g b)).
  + exact: semantic_le_refl.
  + exact: loop_pre_post.
  + have branches i : derives total (mask (eval (g i)) I) (b i) I.
      apply: (@DConsequence total (CQRules.pre total (translate_statement (b i)) I) I
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
move=>Hwf /(proj1 (CQRules.valid_iff _ _ _ _)) Hpre.
apply: (@DConsequence total (CQRules.pre total (translate_statement s) Q) Q P Q s).
- exact: Hpre.
- exact: semantic_le_refl.
- exact: (@derives_pre total s Hwf Q).
Qed.

Theorem translate_sound_complete total P s Q : statement_wf s ->
  (derives total P s Q <-> CQHoare.valid total P (translate_statement s) Q).
Proof. move=>Hwf; split; [exact: derives_translate_sound | exact: derives_translate_complete]. Qed.

End DistributedGuardedRules.
