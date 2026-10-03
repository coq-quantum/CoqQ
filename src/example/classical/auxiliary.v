(* Classical: auxiliary. See README.md and PROOF_NOTES.md. *)
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
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace hspace_extra summable qreg qmem.
From quantum.example.classical Require Import language state assertion semantics hoare.
Module CQInvariant.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


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
Import CQAssertion CQPredicate CQHoare ClassicalLanguage ClassicalLocality ClassicalOperational.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma denote_expression_zero A (e : expression A) c s (rho : 'End(Hq)) t :
  (forall k, expression_variables e k -> k \notin writes c) ->
  0%:VF ⊑ rho -> eval e s <> eval e t -> denote c s t rho = 0.
Proof.
move=>fresh pos diff; rewrite -(operational_denotational c s t pos) /opsum sum_summableE.
  by apply: norm_bounded_cvg; apply: operational_summable.
have Z rt : opfun c s rho rt t = 0.
  rewrite /opfun; case E: (eval_route rt c (s,rho))=>[[u q]|] /=.
  - rewrite /sunit_def; case: eqP=>[ut|//].
    subst u; exfalso; apply: diff.
    exact: terminates_preserves_expression fresh (eval_route_sound E).
  - by [].
under eq_sum do rewrite Z.
exact: summable_sum_cst0.
Qed.

Lemma wp_guard_agree c (b : bool_expr) (P Q : assertion) s :
  (forall k, expression_variables b k -> k \notin writes c) ->
  (forall t, eval b t = eval b s -> P t = Q t) ->
  wp (denote c) P s = wp (denote c) Q s.
Proof.
move=>fresh agree; apply: effect_eq=>rho; rewrite !wp_pairing.
apply: eq_sum=>t.
case: (boolP (eval b t == eval b s))=>[/eqP E|/eqP ne].
- by rewrite (agree t E).
- have Z : denote c s t rho = 0.
    apply (@denote_expression_zero bool b c s rho t fresh (denf_ge0 rho)).
    by move=>E; apply: ne; symmetry.
  by rewrite Z !comp_lfun0r !linear0.
Qed.

Lemma pre_mask_true total c (b : bool_expr) (P : assertion) s :
  (forall k, expression_variables b k -> k \notin writes c) ->
  eval b s = true -> pre total c (mask (eval b) P) s = pre total c P s.
Proof.
move=>fresh bs; case: total.
- apply (@wp_guard_agree c b (mask (eval b) P) P s fresh).
  by move=>t bt; rewrite /mask bt bs.
- have E : wp (denote c) (complement (mask (eval b) P)) s =
      wp (denote c) (complement P) s.
    apply (@wp_guard_agree c b (complement (mask (eval b) P)) (complement P) s fresh)=>t bt.
    by rewrite /complement /mask bt bs.
  apply/val_inj.
  change (\1 - (wp (denote c) (complement (mask (eval b) P)) s : 'End(Hq)) =
    \1 - (wp (denote c) (complement P) s : 'End(Hq))).
  by rewrite E.
Qed.

Lemma valid_invariant total P c Q (b : bool_expr) :
  (forall k, expression_variables b k -> k \notin writes c) ->
  CQHoare.valid total P c Q ->
  CQHoare.valid total (mask (eval b) P) c (mask (eval b) Q).
Proof.
move=>fresh /(proj1 (valid_iff _ _ _ _)) V.
apply/(proj2 (valid_iff _ _ _ _))=>s.
rewrite /mask; case bs: (eval b s); last exact: obsf_ge0.
by rewrite (@pre_mask_true total c b Q s fresh bs); apply: V.
Qed.

Lemma derives_invariant total P c Q (b : bool_expr) :
  (forall k, expression_variables b k -> k \notin writes c) ->
  derives total P c Q -> derives total (mask (eval b) P) c (mask (eval b) Q).
Proof.
move=>fresh /derives_sound V; apply: derives_complete.
exact: valid_invariant fresh V.
Qed.
End CQInvariant.


Module CQAuxiliary.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


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
Import CQAssertion CQAssertionAlgebra CQAssertionSeries CQPredicate CQHoare.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation C := hermitian.C.
Implicit Types P Q : assertion.

Lemma valid_bottom total c : CQHoare.valid total semantic_bottom c semantic_bottom.
Proof. apply/(proj2 (valid_iff _ _ _ _)); exact: semantic_bottom_le. Qed.

Lemma valid_top c : CQHoare.valid false semantic_top c semantic_top.
Proof.
apply/(proj2 (valid_iff _ _ _ _)); rewrite /pre /xp /= wlp_top.
exact: semantic_le_refl.
Qed.

Lemma valid_disjunction total c p q P Q :
  CQHoare.valid total (mask p P) c Q -> CQHoare.valid total (mask q P) c Q ->
  CQHoare.valid total (mask (predU p q) P) c Q.
Proof.
move=>/(proj1 (valid_iff _ _ _ _)) Vp /(proj1 (valid_iff _ _ _ _)) Vq.
apply/(proj2 (valid_iff _ _ _ _)); exact: mask_or_le Vp Vq.
Qed.

Lemma valid_disjoint_sum total c (p q : pred cmem) (P Q R S : assertion) :
  (forall i, q i -> ~~ p i) ->
  (forall i, (S i : 'End(Hq)) = (mask p P i : 'End(Hq)) + (mask q Q i : 'End(Hq))) ->
  CQHoare.valid total (mask p P) c R -> CQHoare.valid total (mask q Q) c R ->
  CQHoare.valid total S c R.
Proof.
move=>disj SE /(proj1 (valid_iff _ _ _ _)) Vp /(proj1 (valid_iff _ _ _ _)) Vq.
apply/(proj2 (valid_iff _ _ _ _)); exact: mask_disjoint_sum_le disj SE Vp Vq.
Qed.

Lemma valid_sup total c (F : nat -> assertion) Q :
  semantic_chain F -> (forall n, CQHoare.valid total (F n) c Q) ->
  CQHoare.valid total (semantic_sup F) c Q.
Proof.
move=>inc VF; apply/(proj2 (valid_iff _ _ _ _)).
exact (@semantic_sup_least cmem Hq F (pre total c Q) inc
  (fun n => (proj1 (valid_iff total (F n) c Q)) (VF n))).
Qed.

Lemma valid_finite_linear_total (J : finType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, CQHoare.valid true (F j) c (G j)) -> CQHoare.valid true P c Q.
Proof.
move=>wn PE QE V rho.
rewrite (@expect_finite_linear cmem Hq J w F P rho PE)
  (@expect_finite_linear cmem Hq J w G Q (CQHoare.run c rho) QE).
by apply: ler_sum=>j _; apply: ler_wpM2l; [apply: wn | apply: V].
Qed.

Lemma valid_finite_linear_partial (J : finType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) -> (\sum_j w j <= 1) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, CQHoare.valid false (F j) c (G j)) -> CQHoare.valid false P c Q.
Proof.
move=>wn wb PE QE V; apply/CQHoare.valid_partial_loss=>rho.
rewrite (@expect_finite_linear cmem Hq J w F P rho PE)
  (@expect_finite_linear cmem Hq J w G Q (CQHoare.run c rho) QE) -addrA.
pose loss := CQState.mass rho - CQState.mass (CQHoare.run c rho).
have lp : 0 <= loss by rewrite /loss subr_ge0; exact: CQKernel.apply_mass.
apply: (le_trans (y := \sum_j w j * (expect (G j) (CQHoare.run c rho) + loss))).
- apply: ler_sum=>j _; apply: ler_wpM2l; first exact: wn.
  by move: ((proj1 (CQHoare.valid_partial_loss _ _ _) (V j)) rho); rewrite -addrA.
- under eq_bigr do rewrite mulrDr.
  rewrite big_split /= -mulr_suml lerD2l.
  by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r.
Qed.

Lemma valid_series_total (J : choiceType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, CQHoare.valid true (F j) c (G j)) -> CQHoare.valid true P c Q.
Proof.
move=>wn SF SG PE QE V rho.
rewrite (@expect_series cmem J Hq w F P wn SF PE rho)
  (@expect_series cmem J Hq w G Q wn SG QE (CQHoare.run c rho)).
rewrite /sum; apply: ler_etlim.
- apply: norm_bounded_cvg; exact: (@expect_series_summable cmem J Hq w F P wn SF PE rho).
- apply: norm_bounded_cvg; exact: (@expect_series_summable cmem J Hq w G Q wn SG QE (CQHoare.run c rho)).
- move=>A; apply: ler_sum=>j _.
  by apply: ler_wpM2l; [apply: wn | apply: V].
Qed.

Lemma valid_series_partial (J : choiceType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) -> summable w -> sum w <= 1 ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, CQHoare.valid false (F j) c (G j)) -> CQHoare.valid false P c Q.
Proof.
move=>wn sw wb SF SG PE QE V; apply/CQHoare.valid_partial_loss=>rho.
rewrite (@expect_series cmem J Hq w F P wn SF PE rho)
  (@expect_series cmem J Hq w G Q wn SG QE (CQHoare.run c rho)) -addrA.
pose loss := CQState.mass rho - CQState.mass (CQHoare.run c rho).
have lp : 0 <= loss by rewrite /loss subr_ge0; exact: CQKernel.apply_mass.
pose g := Summable.build (@expect_series_summable cmem J Hq w G Q wn SG QE (CQHoare.run c rho)).
pose weights := Summable.build sw.
have E j : (g + loss *: weights) j = w j * (expect (G j) (CQHoare.run c rho) + loss).
  change (w j * expect (G j) (CQHoare.run c rho) + loss * w j =
    w j * (expect (G j) (CQHoare.run c rho) + loss)).
  by rewrite mulrDr [loss * _]mulrC.
apply: (le_trans (y := sum (g + loss *: weights))).
- rewrite /sum; apply: ler_etlim.
  + apply: norm_bounded_cvg; exact: (@expect_series_summable cmem J Hq w F P wn SF PE rho).
  + exact: summable_cvg.
  + move=>A; apply: ler_sum=>j _; rewrite E.
    apply: ler_wpM2l; first exact: wn.
    by move: ((proj1 (CQHoare.valid_partial_loss _ _ _) (V (val j))) rho); rewrite -addrA.
- rewrite summable_sumD summable_sumZ /g /= lerD2l.
  change (loss * sum w <= loss).
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l.
Qed.

Lemma derives_bottom total c : derives total semantic_bottom c semantic_bottom.
Proof. apply: derives_complete; exact: valid_bottom. Qed.
Lemma derives_top c : derives false semantic_top c semantic_top.
Proof. apply: derives_complete; exact: valid_top. Qed.
Lemma derives_disjunction total c p q P Q :
  derives total (mask p P) c Q -> derives total (mask q P) c Q ->
  derives total (mask (predU p q) P) c Q.
Proof.
move=>/derives_sound Vp /derives_sound Vq; apply: derives_complete.
exact: valid_disjunction Vp Vq.
Qed.
End CQAuxiliary.


Module CQParameterized.
(* Finite parameter and register selection, classical paper pp. 16, 23, 31.
   The Param rule uses the correct wp formula; see C4 in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage CQAssertion CQPredicate QRegAuto.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Section Selector.
Variable I : finType.
Variable choose : expression (option I).
Variable branch : I -> command.

Definition selector_guard (i : I) := EApp (EConst (fun a : option I => a == Some i)) choose.
Definition selector_list indices :=
  foldr (fun i tail => Conditional (selector_guard i) (branch i) tail) Abort indices.
Definition selector_command := selector_list (enum I).
Definition selector_pre (Q : assertion) m : 'FO(Hq) :=
  if eval choose m is Some i then CQHoare.pre true (branch i) Q m else 0%:VF.

Lemma selector_list_selected indices i m Q : i \in indices -> eval choose m = Some i ->
  CQHoare.pre true (selector_list indices) Q m = CQHoare.pre true (branch i) Q m.
Proof.
elim: indices=>[|j rest IH]; first by rewrite in_nil.
rewrite inE=>/orP[/eqP->|Hi] He.
- change (CQHoare.pre true (Conditional (selector_guard j) (branch j) (selector_list rest)) Q m =
    CQHoare.pre true (branch j) Q m).
  by rewrite CQHoare.pre_conditional /conditional /selector_guard /eval /= -/(eval choose m) He eqxx.
- change (CQHoare.pre true (Conditional (selector_guard j) (branch j) (selector_list rest)) Q m =
    CQHoare.pre true (branch i) Q m).
  rewrite CQHoare.pre_conditional /conditional /selector_guard /eval /= -/(eval choose m) He /=.
  case: eqP=>[Eij|Hne].
  + by case: Eij=>->.
  + exact: IH Hi He.
Qed.

Lemma selector_list_none indices m Q : eval choose m = None ->
  CQHoare.pre true (selector_list indices) Q m = 0%:VF.
Proof.
move=>He; elim: indices=>[|i rest IH].
- by rewrite /selector_list /CQHoare.pre /xp /= wp_abort.
- change (CQHoare.pre true (Conditional (selector_guard i) (branch i) (selector_list rest)) Q m = 0%:VF).
  by rewrite CQHoare.pre_conditional /conditional /selector_guard /eval /= -/(eval choose m) He.
Qed.

Lemma selector_preE Q : CQHoare.pre true selector_command Q = selector_pre Q.
Proof.
apply/funext=>m; rewrite /selector_pre.
case He: (eval choose m)=>[i|].
- apply: selector_list_selected He; exact: mem_enum.
- exact: selector_list_none He.
Qed.

Lemma selector_pre_sum Q m : (selector_pre Q m : 'End(Hq)) =
  \sum_(i : I) (if eval choose m == Some i then (CQHoare.pre true (branch i) Q m : 'End(Hq)) else 0).
Proof.
rewrite /selector_pre; case He: (eval choose m)=>[i|] /=.
- rewrite (bigD1 i) //= eqxx big1 ?addr0 // =>j Hji.
  by rewrite (inj_eq Some_inj) eq_sym (negbTE Hji).
- by rewrite big1.
Qed.

Lemma selector_list_abort indices m : eval choose m = None ->
  denote (selector_list indices) m = abort_sem m.
Proof.
move=>He; elim: indices=>[|i rest IH] //=.
by rewrite /selector_list /= /if_sem /selector_guard /eval /= -/(eval choose m) He.
Qed.

Lemma selector_abort m : eval choose m = None -> denote selector_command m = abort_sem m.
Proof. exact: selector_list_abort. Qed.

Theorem valid_selector total Q : CQHoare.valid total (selector_pre Q) selector_command Q.
Proof. apply: CQHoare.valid_from_total; rewrite -selector_preE; exact: CQHoare.pre_valid. Qed.

Theorem derives_selector total Q : CQHoare.derives total (selector_pre Q) selector_command Q.
Proof. apply: CQHoare.derives_complete; exact: valid_selector. Qed.
End Selector.

Definition decode (I : finType) (A : eqType) (key : I -> A) (x : A) := [pick i | x == key i].

Lemma decode_some (I : finType) (A : eqType) (key : I -> A) x i :
  decode key x = Some i -> x = key i.
Proof. rewrite /decode; case: pickP=>[j /eqP Hj|Hnone] // [= <-]; exact: Hj. Qed.

Lemma decode_eq (I : finType) (A : eqType) (key : I -> A) : injective key ->
  forall x i, (decode key x == Some i) = (x == key i).
Proof.
move=>Hinj x i; apply/idP/idP.
- move/eqP/decode_some=>->; exact: eqxx.
- move/eqP=>Hx; rewrite /decode; case: pickP=>[j /eqP Hj|Hnone].
  + have -> : j = i by apply: Hinj; rewrite -Hx -Hj.
    exact: eqxx.
  + by move: (Hnone i); rewrite Hx eqxx.
Qed.

Lemma one_based_inj n : injective (fun i : 'I_n => Posz (val i).+1).
Proof. move=>i j [= Hij]; apply/val_inj; exact: Hij. Qed.

Definition parameter_selector K (e : expression int) : expression (option 'I_K) :=
  EApp (EConst (decode (fun i : 'I_K => Posz (val i).+1))) e.

Lemma parameter_selector_eq K e m (i : 'I_K) :
  (eval (parameter_selector K e) m == Some i) = (eval e m == Posz (val i).+1).
Proof.
rewrite /parameter_selector eval_app eval_const.
exact: (@decode_eq _ _ (fun j : 'I_K => Posz (val j).+1)
  (@one_based_inj K) (eval e m) i).
Qed.

Definition parameterized_unitary t K (q : wf_qreg t) (U : 'I_K -> 'FU('Ht t)) e :=
  selector_command (parameter_selector K e) (fun i => Unitary q (EConst (U i))).
Definition parameterized_pre t K (q : wf_qreg t) (U : 'I_K -> 'FU('Ht t)) e Q :=
  selector_pre (parameter_selector K e) (fun i => Unitary q (EConst (U i))) Q.

Theorem parameterized_wp t K (q : wf_qreg t) U e Q m :
  (CQHoare.pre true (parameterized_unitary q U e) Q m : 'End(Hq)) =
  \sum_(i : 'I_K) (if eval e m == Posz (val i).+1 then
    (liftfso (formso (tf2f q q (U i))))^*o (Q m) else 0).
Proof.
rewrite selector_preE selector_pre_sum; apply: eq_bigr=>i _.
rewrite parameter_selector_eq; case: ifP=>// _.
exact: CQPrimitive.unitary_pre.
Qed.

Theorem derives_parameterized total t K (q : wf_qreg t) (U : 'I_K -> 'FU('Ht t)) e Q :
  CQHoare.derives total (parameterized_pre q U e Q) (parameterized_unitary q U e) Q.
Proof. exact: derives_selector. Qed.

Definition distinct_indices n k := {r : k.-tuple 'I_n | uniq r}.

Lemma selected_register_valid n k T (q : wf_qreg T.[n]) (r : distinct_indices n k) :
  valid_qreg (qreg_tuple (fun j => qreg_tuplei (tnth (val r) j) q)).
Proof.
apply: valid_qreg_tuple.
- move=>j; apply: valid_qreg_tuplei; exact: qreg_is_valid.
- move=>i j Hij; rewrite disjoint_qregIE !eval_indexE.
  apply: disjoint_qregP_abs; first exact: qreg_is_valid.
  have Hne : tnth (val r) i != tnth (val r) j.
    apply/negP=>/eqP H; move/tuple_uniqP: (valP r)=>/(_ _ _ H) E.
    by move: Hij; rewrite E eqxx.
  by rewrite /= Hne.
Qed.

Definition selected_register n k T (q : wf_qreg T.[n]) (r : distinct_indices n k) : wf_qreg T.[k] :=
  WF_QReg (selected_register_valid q r).

Definition selection_key n k K (a : distinct_indices n k * 'I_K) :=
  ([ffun j => Posz (val (tnth (val a.1) j)).+1], Posz (val a.2).+1).

Lemma selection_key_inj n k K : injective (@selection_key n k K).
Proof.
move=>[r i] [t j] Ekey.
have Ef := congr1 fst Ekey; have Ez := congr1 snd Ekey.
congr (_, _); last exact: (@one_based_inj K i j Ez).
apply/val_inj/eq_from_tnth=>x; apply: one_based_inj.
have H := congr1 (fun f : {ffun 'I_k -> int} => f x) Ef.
by move: H; rewrite /selection_key /= !ffunE.
Qed.

Definition register_selector n k K (es : 'I_k -> expression int) (e : expression int) :
    expression (option (distinct_indices n k * 'I_K)) :=
  EApp (EApp (EConst (fun f z => decode (@selection_key n k K) ([ffun j => f j],z)))
    (ELam es)) e.

Lemma register_selector_eq n k K es e m (a : distinct_indices n k * 'I_K) :
  (eval (register_selector n K es e) m == Some a) =
  (([forall j, eval (es j) m == Posz (val (tnth (val a.1) j)).+1]) &&
    (eval e m == Posz (val a.2).+1)).
Proof.
rewrite /register_selector /eval /= (decode_eq (@selection_key_inj n k K)) /selection_key /=.
rewrite xpair_eqE; congr (_ && _); apply/idP/idP.
- move/eqP=>H; apply/forallP=>j; apply/eqP.
  have E := congr1 (fun f : {ffun 'I_k -> int} => f j) H.
  by move: E; rewrite !ffunE.
- move/forallP=>H; apply/eqP/ffunP=>j; rewrite !ffunE; exact/eqP/H.
Qed.

Definition selected_unitary n k K T (q : wf_qreg T.[n]) (U : 'I_K -> 'FU('Ht T.[k]))
    (es : 'I_k -> expression int) e :=
  selector_command (register_selector n K es e)
    (fun a => Unitary (selected_register q a.1) (EConst (U a.2))).
Definition selected_pre n k K T (q : wf_qreg T.[n]) (U : 'I_K -> 'FU('Ht T.[k]))
    (es : 'I_k -> expression int) e Q :=
  selector_pre (register_selector n K es e)
    (fun a => Unitary (selected_register q a.1) (EConst (U a.2))) Q.

Theorem selected_wp n k K T (q : wf_qreg T.[n]) (U : 'I_K -> 'FU('Ht T.[k])) es e Q m :
  (CQHoare.pre true (selected_unitary q U es e) Q m : 'End(Hq)) =
  \sum_(a : distinct_indices n k * 'I_K)
    (if ([forall j, eval (es j) m == Posz (val (tnth (val a.1) j)).+1]) &&
      (eval e m == Posz (val a.2).+1) then
      (liftfso (formso (tf2f (selected_register q a.1) (selected_register q a.1) (U a.2))))^*o (Q m)
    else 0).
Proof.
rewrite selector_preE selector_pre_sum; apply: eq_bigr=>a _.
rewrite register_selector_eq; case: ifP=>// _; exact: CQPrimitive.unitary_pre.
Qed.

Theorem valid_param total n k K T (q : wf_qreg T.[n]) (U : 'I_K -> 'FU('Ht T.[k])) es e Q :
  CQHoare.valid total (selected_pre q U es e Q) (selected_unitary q U es e) Q.
Proof. exact: valid_selector. Qed.
Theorem derives_param total n k K T (q : wf_qreg T.[n]) (U : 'I_K -> 'FU('Ht T.[k])) es e Q :
  CQHoare.derives total (selected_pre q U es e Q) (selected_unitary q U es e) Q.
Proof. exact: derives_selector. Qed.


Lemma parameter_selector_zero K m :
  eval (parameter_selector K (EConst (0 : int))) m = None.
Proof.
rewrite /parameter_selector eval_app !eval_const /decode.
case: pickP=>[i Hi|Hnone] //.
Qed.

Lemma parameterized_zero_abort t K (q : wf_qreg t) (U : 'I_K -> 'FU('Ht t)) m :
  denote (parameterized_unitary q U (EConst (0 : int))) m = abort_sem m.
Proof. apply: selector_abort; exact: parameter_selector_zero. Qed.

Theorem selected_pre_sum n k K T (q : wf_qreg T.[n]) (U : 'I_K -> 'FU('Ht T.[k])) es e Q m :
  (selected_pre q U es e Q m : 'End(Hq)) =
  \sum_(a : distinct_indices n k * 'I_K)
    (if ([forall j, eval (es j) m == Posz (val (tnth (val a.1) j)).+1]) &&
      (eval e m == Posz (val a.2).+1) then
      (liftfso (formso (tf2f (selected_register q a.1) (selected_register q a.1) (U a.2))))^*o (Q m)
    else 0).
Proof. rewrite /selected_pre -selector_preE; exact: selected_wp. Qed.

Lemma register_selector_duplicate n k K es e m (j l : 'I_k) :
  j != l -> eval (es j) m = eval (es l) m ->
  eval (register_selector n K es e) m = None.
Proof.
move=>Hne Ejl; case E: (eval (register_selector n K es e) m)=>[a|] //.
have Hmatch : eval (register_selector n K es e) m == Some a by rewrite E.
move: Hmatch; rewrite register_selector_eq=>/andP[/forallP Hall _].
have Er : tnth (val a.1) j = tnth (val a.1) l.
  apply: one_based_inj.
  by rewrite -(eqP (Hall j)) -(eqP (Hall l)) Ejl.
have Ej : j = l by move/tuple_uniqP: (valP a.1)=>/(_ _ _ Er).
by move: Hne; rewrite Ej eqxx.
Qed.

Lemma selected_duplicate_abort n k K T (q : wf_qreg T.[n]) (U : 'I_K -> 'FU('Ht T.[k]))
    es e m (j l : 'I_k) :
  j != l -> eval (es j) m = eval (es l) m ->
  denote (selected_unitary q U es e) m = abort_sem m.
Proof.
move=>Hne Ejl; apply: selector_abort.
exact: (@register_selector_duplicate n k K es e m j l Hne Ejl).
Qed.
End CQParameterized.


Module CQProbabilisticComposition.
(* Probabilistic composition via saturated projector support. See PROOF_NOTES.md. *)


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
Import CQAssertion CQExpectation CQPredicate CQHoare ClassicalLanguage.
Local Open Scope hspace_scope.
Local Notation C := hermitian.C.

Section Support.
Context {I : choiceType} {H : chsType}.
Definition projection_assertion (P : I -> {hspace H}) : I -> 'FO(H) :=
  fun i => [obs of P i].

Lemma expect_term_le_expect (P : I -> 'FO(H)) (rho : @CQState.state I H) i :
  expect_term P rho i <= expect P rho.
Proof.
pose terms := Summable.build (expect_summable P rho).
have B := psum_norm_ler_norm terms [fset i]%fset.
have E : psum (fun j => `|terms j|) = psum terms.
  apply: psum_abs_ge0E=>j; exact: expect_term_ge0.
move: B; rewrite psum1 /summable_norm E.
change (`|expect_term P rho i| <= expect P rho ->
  expect_term P rho i <= expect P rho).
by rewrite ger0_norm ?expect_term_ge0.
Qed.

Lemma expect_zero_term (P : I -> 'FO(H)) (rho : @CQState.state I H) :
  expect P rho = 0 -> forall i, expect_term P rho i = 0.
Proof.
move=>E i; apply/eqP; rewrite eq_le expect_term_ge0 andbT.
by move: (expect_term_le_expect P rho i); rewrite E.
Qed.

Lemma projection_saturated_support (P : I -> {hspace H})
    (rho : @CQState.state I H) :
  expect (projection_assertion P) rho = CQState.mass rho ->
  forall i, supph (rho i) `<=` P i.
Proof.
move=>E i.
have Ec : expect (complement (projection_assertion P)) rho = 0.
  by rewrite expect_complement -CQState.mass_trace E subrr.
have Ei := expect_zero_term Ec i.
have Hr : rho i \is psdlf by rewrite psdlfE vdistr_ge0.
apply: (@supph_trlf0_le H (PsdLf_Build Hr) (P i)).
move: Ei; rewrite /expect_term /complement /projection_assertion /=.
by rewrite lftraceC hscmpltE.
Qed.

Lemma support_compr (r : 'F+(H)) (P : {hspace H}) :
  supph r `<=` P -> (r : 'End(H)) \o P = r.
Proof.
move=>HP; move: HP; rewrite leh_compl=>/eqP HP.
rewrite -{1}(suppvlf (r : 'End(H))) -comp_lfunA.
move: HP; rewrite /supph !hsE /= =>HP.
by rewrite HP suppvlf.
Qed.

Lemma support_compl (r : 'F+(H)) (P : {hspace H}) :
  supph r `<=` P -> P \o (r : 'End(H)) = r.
Proof.
move=>Hsupport; have E := support_compr Hsupport.
by move: (f_equal (fun A : 'End(H) => A^A) E); rewrite adjf_comp !hermf_adjE.
Qed.

Lemma supported_pairing (r : 'F+(H)) (P : {hspace H}) (M : 'End(H)) a :
  supph r `<=` P -> P \o M \o P = a *: (P : 'End(H)) ->
  \Tr (M \o r) = a * \Tr r.
Proof.
move=>Hs HM.
have RP := support_compr Hs.
have PR := support_compl Hs.
rewrite -{1}RP comp_lfunA.
rewrite [\Tr ((M \o r) \o P)]lftraceC comp_lfunA.
rewrite -{1}PR comp_lfunA HM linearZl /= linearZ /= PR.
by [].
Qed.

Lemma saturated_expectation (P : I -> {hspace H}) (M : I -> 'FO(H)) a
    (rho : @CQState.state I H) :
  expect (projection_assertion P) rho = CQState.mass rho ->
  (forall i, P i \o M i \o P i = a *: (P i : 'End(H))) ->
  expect M rho = a * CQState.mass rho.
Proof.
move=>E HM.
pose terms := Summable.build (expect_summable (@semantic_top I H) rho).
have Et : sum terms = CQState.mass rho.
  change (expect semantic_top rho = CQState.mass rho).
  by rewrite expect_identity CQState.mass_trace.
have TE : expect_term M rho = a *: terms.
  apply/funext=>i.
  have Hr : rho i \is psdlf by rewrite psdlfE vdistr_ge0.
  change (\Tr (M i \o rho i) = a * \Tr (\1 \o rho i)).
  rewrite comp_lfun1l.
  exact: (supported_pairing (r := PsdLf_Build Hr) (M := M i)
    (projection_saturated_support E i) (HM i)).
by rewrite /expect TE summable_sumZ Et.
Qed.
End Support.

Section Rule.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem valid_probcomp_projection (p : pred cmem) (P : cmem -> {hspace Hq})
    (M R Q : assertion) (a : C) c d :
  (forall s, (R s : 'End(Hq)) = if p s then a *: \1 else 0) ->
  (forall s, P s \o M s \o P s = a *: (P s : 'End(Hq))) ->
  CQHoare.valid true (mask p semantic_top) c (projection_assertion P) ->
  CQHoare.valid true M d Q ->
  CQHoare.valid true R (Sequence c d) Q.
Proof.
move=>RE HM Vc Vd; apply/(proj2 (valid_total_iff _ _ _))=>s.
apply/lef_trden=>rho; rewrite /wp_command wp_point.
change (\Tr (R s \o rho) <=
  expect Q (CQHoare.run (Sequence c d) (CQState.point s rho))).
rewrite CQHoare.run_sequence RE.
case Ep: (p s); last by rewrite comp_lfun0l linear0; apply: expect_ge0.
rewrite linearZl /= linearZ /= comp_lfun1l.
pose output := CQHoare.run c (CQState.point s rho).
have Hfirst : \Tr rho <= expect (projection_assertion P) output.
  have H := Vc (CQState.point s rho).
  by move: H; rewrite expect_point /mask Ep comp_lfun1l.
have Hexp : expect (projection_assertion P) output <= CQState.mass output.
  by rewrite CQState.mass_trace; apply: expect_le_trace.
have Hmass : CQState.mass output <= \Tr rho.
  rewrite -(CQState.point_mass s rho); exact: CQKernel.apply_mass.
have EM : CQState.mass output = \Tr rho.
  by apply/eqP; rewrite eq_le Hmass (le_trans Hfirst Hexp).
have ES : expect (projection_assertion P) output = CQState.mass output.
  by apply/eqP; rewrite eq_le Hexp EM Hfirst.
have EV := saturated_expectation ES HM.
have Hsecond := Vd output.
by move: Hsecond; rewrite EV EM.
Qed.

Theorem derives_probcomp_projection (p : pred cmem) (P : cmem -> {hspace Hq})
    (M R Q : assertion) (a : C) c d :
  (forall s, (R s : 'End(Hq)) = if p s then a *: \1 else 0) ->
  (forall s, P s \o M s \o P s = a *: (P s : 'End(Hq))) ->
  derives true (mask p semantic_top) c (projection_assertion P) ->
  derives true M d Q -> derives true R (Sequence c d) Q.
Proof.
move=>RE HM /derives_sound Vc /derives_sound Vd; apply: derives_complete.
exact: valid_probcomp_projection RE HM Vc Vd.
Qed.
End Rule.
End CQProbabilisticComposition.


Module CQAssertionLocality.
(* Predicate-transformer locality and existential elimination. See PROOF_NOTES.md. *)


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
Import CQAssertion CQPredicate CQHoare ClassicalLanguage ClassicalFootprint.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition assertion_local (X : set identifier) (P : assertion) :=
  forall s t, agree_on X s t -> P s = P t.

Lemma agree_on_update X u (x : variable u) v s t :
  agree_on X s t -> agree_on X (s.[x <- v])%M (t.[x <- v])%M.
Proof.
move=>H w y Hy.
rewrite /cmset /cmget /cvtype /= /orapp.
case: eqP=>E; last exact: H Hy.
case: (cvname x == cvname y)=>//; exact: H Hy.
Qed.

Lemma agree_on_external X u (x : variable u) v s :
  ~ X (key x) -> agree_on X s (s.[x <- v])%M.
Proof.
move=>H w y Hy; apply: ClassicalLocality.update_unchanged.
rewrite inE; apply/negP=>/eqP E; apply: H; by rewrite -E.
Qed.

Lemma eval_agree A (e : expression A) X s t :
  (expression_variables e `<=` X)%classic ->
  agree_on X s t -> eval e s = eval e t.
Proof. move=>Hsub Hst; apply: eval_local=>u x Hx; exact: Hst (Hsub _ Hx). Qed.

Theorem pre_local total c X Q :
  (variables c `<=` X)%classic -> assertion_local X Q ->
  assertion_local X (pre total c Q).
Proof.
elim: c Q=>[| |u x e|u x p|u v x q M|u q phi|u q U|
    c IH d IHd|b c IH d IHd|b c IH] Q Hsub HQ s t Hst.
- by rewrite /pre /= xp_skip; exact: HQ.
- by case Etotal: total; rewrite /pre /= /xp ?Etotal ?wp_abort ?wlp_abort.
- have Ee : eval e s = eval e t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by right.
  apply/val_inj.
  change ((pre total (Assign x e) Q s : 'End(Hq)) = (pre total (Assign x e) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.assign_pre Ee.
  by rewrite (HQ _ _ (@agree_on_update X u x (eval e t) s t Hst)).
- have Ep : eval (probability_expression p) s = eval (probability_expression p) t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by right.
  apply/val_inj.
  change ((pre total (Random x p) Q s : 'End(Hq)) = (pre total (Random x p) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.random_pre.
  apply: eq_sum=>a; rewrite /probability_mass -/(eval _ s) -/(eval _ t) Ep.
  by rewrite (HQ _ _ (@agree_on_update X u x a s t Hst)).
- have EM : eval M s = eval M t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by right.
  apply/val_inj.
  change ((pre total (Measure x q M) Q s : 'End(Hq)) = (pre total (Measure x q M) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.measurement_pre.
  apply: eq_bigr=>a _; rewrite -/(eval M s) -/(eval M t) EM.
  by rewrite (HQ _ _ (@agree_on_update X (QType u) x a s t Hst)).
- have Ephi := eval_agree Hsub Hst.
  apply/val_inj.
  change ((pre total (Initialize q phi) Q s : 'End(Hq)) = (pre total (Initialize q phi) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.initial_pre.
  by rewrite -/(eval phi s) -/(eval phi t) Ephi (HQ _ _ Hst).
- have EU := eval_agree Hsub Hst.
  apply/val_inj.
  change ((pre total (Unitary q U) Q s : 'End(Hq)) = (pre total (Unitary q U) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.unitary_pre.
  by rewrite -/(eval U s) -/(eval U t) EU (HQ _ _ Hst).
- rewrite !pre_sequence; apply: IH Hst.
  + move=>k Hk; apply: Hsub; by left.
  + apply: IHd HQ; move=>k Hk; apply: Hsub; by right.
- have Eb : eval b s = eval b t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by left.
  rewrite !pre_conditional /conditional -/(eval b s) -/(eval b t) Eb.
  case: (eval b t); [apply: (IH Q _ HQ s t Hst)|apply: (IHd Q _ HQ s t Hst)];
    move=>k Hk; apply: Hsub; right; [by left|by right].
- have Hb : (expression_variables b `<=` X)%classic.
    move=>k Hk; apply: Hsub; by left.
  have Hc : (variables c `<=` X)%classic.
    move=>k Hk; apply: Hsub; by right.
  have HU n : assertion_local X (pre total (unroll b c n) Q).
    elim: n=>[|n IHn] a d Had.
    + by case Etotal: total; rewrite /pre /= /xp ?Etotal ?wp_abort ?wlp_abort.
    + rewrite !pre_unrollS /conditional -/(eval b a) -/(eval b d)
        (eval_agree Hb Had).
      case: (eval b d); [exact: (IH _ Hc IHn a d Had)|exact: (HQ a d Had)].
  apply/val_inj.
  change ((pre total (While b c) Q s : 'End(Hq)) = (pre total (While b c) Q t : 'End(Hq))).
  case Etotal: total HU=>HU.
  + change ((wp_command (While b c) Q s : 'End(Hq)) = (wp_command (While b c) Q t : 'End(Hq))).
    have Cs := @wp_unroll_cvg b c Q s.
    have Ct := @wp_unroll_cvg b c Q t.
    have E : (fun n => (wp_command (unroll b c n) Q s : 'End(Hq))) =
        (fun n => (wp_command (unroll b c n) Q t : 'End(Hq))).
      apply/funext=>n; exact: (congr1 (fun f : 'FO(Hq) => (f : 'End(Hq))) (HU n s t Hst)).
    by rewrite -(cvg_lim (@norm_hausdorff _ _) Cs) E
      (cvg_lim (@norm_hausdorff _ _) Ct).
  + change ((wlp_command (While b c) Q s : 'End(Hq)) = (wlp_command (While b c) Q t : 'End(Hq))).
    have Cs := @wlp_unroll_cvg b c Q s.
    have Ct := @wlp_unroll_cvg b c Q t.
    have E : (fun n => (wlp_command (unroll b c n) Q s : 'End(Hq))) =
        (fun n => (wlp_command (unroll b c n) Q t : 'End(Hq))).
      apply/funext=>n; exact: (congr1 (fun f : 'FO(Hq) => (f : 'End(Hq))) (HU n s t Hst)).
    by rewrite -(cvg_lim (@norm_hausdorff _ _) Cs) E
      (cvg_lim (@norm_hausdorff _ _) Ct).
Qed.


Definition exists_update u (x : variable u) (p : pred cmem) : pred cmem :=
  fun s => asbool (exists v, p (s.[x <- v])%M).

Theorem valid_exist total u (x : variable u) (p : pred cmem)
    (M : 'FO(Hq)) c Q X :
  (variables c `<=` X)%classic -> ~ X (key x) -> assertion_local X Q ->
  CQHoare.valid total (mask p (fun _ => M)) c Q ->
  CQHoare.valid total (mask (exists_update x p) (fun _ => M)) c Q.
Proof.
move=>Hc Hx HQ /(proj1 (valid_iff _ _ _ _)) V.
apply/(proj2 (valid_iff _ _ _ _))=>s.
rewrite /mask; case E: (exists_update x p s); last exact: obsf_ge0.
have /asboolP[v Hv] : asbool (exists v, p (s.[x <- v])%M) by exact E.
have Hpre := @pre_local total c X Q Hc HQ s (s.[x <- v])%M
  (@agree_on_external X u x v s Hx).
have := V (s.[x <- v])%M; by rewrite /mask Hv -Hpre.
Qed.

Theorem derives_exist total u (x : variable u) (p : pred cmem)
    (M : 'FO(Hq)) c Q X :
  (variables c `<=` X)%classic -> ~ X (key x) -> assertion_local X Q ->
  derives total (mask p (fun _ => M)) c Q ->
  derives total (mask (exists_update x p) (fun _ => M)) c Q.
Proof.
move=>Hc Hx HQ /derives_sound V; apply: derives_complete.
exact: valid_exist Hc Hx HQ V.
Qed.
End CQAssertionLocality.


Module CQClassicalRanking.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


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
Import CQAssertion CQPredicate CQHoare ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma wp_certain_mask (K : semType cmem cmem Hq Hq) (g : pred cmem)
    (Q : assertion) s :
  (\1 : 'End(Hq)) <= wp K (mask g semantic_top) s ->
  wp K (mask g Q) s = wp K Q s.
Proof.
move=>Hg.
have Eg : (wp K (mask g semantic_top) s : 'End(Hq)) = \1.
  by apply/eqP; rewrite eq_le Hg obsf_le1.
have Ed : (wp K (mask (predC g) semantic_top) s : 'End(Hq)) =
    (wp K semantic_top s : 'End(Hq)) - \1.
  rewrite -Eg; apply: wp_difference=>t.
  by rewrite /mask /predC /=; case: (g t); rewrite /= ?subrr ?subr0.
have Zg : (wp K (mask (predC g) semantic_top) s : 'End(Hq)) = 0.
  apply/eqP; rewrite eq_le obsf_ge0 andbT Ed subv_le0; exact: obsf_le1.
have Zq : (wp K (mask (predC g) Q) s : 'End(Hq)) = 0.
  have Hmono : semantic_le (mask (predC g) Q) (mask (predC g) semantic_top).
    apply: CQAssertionAlgebra.mask_le; exact: semantic_le_top.
  have Le := wp_mono K Hmono s.
  rewrite Zg in Le.
  by apply/eqP; rewrite eq_le Le obsf_ge0.
apply/val_inj.
change ((wp K (mask g Q) s : 'End(Hq)) = (wp K Q s : 'End(Hq))).
have E : (wp K (mask g Q) s : 'End(Hq)) =
    (wp K Q s : 'End(Hq)) - (wp K (mask (predC g) Q) s : 'End(Hq)).
  apply: wp_difference=>t.
  by rewrite /mask /predC /=; case: (g t); rewrite /= ?subrr ?subr0.
by rewrite E Zq subr0.
Qed.

Theorem valid_classical_while (P : assertion) (p : pred cmem)
    (rank : cmem -> nat) b c :
  semantic_le P (mask p semantic_top) ->
  CQHoare.valid true (mask (eval b) P) c P ->
  (forall k, CQHoare.valid true
    (mask (fun s => eval b s && p s && (rank s == k)) semantic_top) c
    (mask (fun s => ~~ p s || (rank s < k)%N) semantic_top)) ->
  CQHoare.valid true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>support /(proj1 (valid_total_iff _ _ _)) inv decrease.
pose Q := mask (predC (eval b)) P.
have bound k : forall s, p s -> (rank s < k)%N ->
    (P s : 'End(Hq)) <= pre true (While b c) Q s.
  elim: k=>[|k IH] s ps Hrank; first by rewrite ltn0 in Hrank.
  rewrite pre_while_unfold /conditional.
  case bs: (esem b s); last by rewrite /Q /mask /predC /eval /= bs.
  change ((P s : 'End(Hq)) <= wp (denote c) (pre true (While b c) Q) s).
  pose g := fun t => ~~ p t || (rank t < rank s)%N.
  have Hcertain : (\1 : 'End(Hq)) <= wp (denote c) (mask g semantic_top) s.
    have H := ((proj1 (valid_total_iff _ _ _)) (decrease (rank s))) s.
    by rewrite /mask /eval bs ps eqxx /= in H.
  have Emask := wp_certain_mask P Hcertain.
  apply: (le_trans (y := (wp (denote c) P s : 'End(Hq)))).
  - by move: (inv s); rewrite /mask /eval bs.
  - have Hmono : semantic_le (mask g P) (pre true (While b c) Q).
      move=>t.
      rewrite /mask; case gt: (g t); last exact: obsf_ge0.
      case pt: (p t).
      + have Hlower : (rank t < rank s)%N by move: gt; rewrite /g pt.
        apply: (IH t pt); exact: ltn_leq_trans Hlower Hrank.
      + apply: (le_trans (y := (0 : 'End(Hq)))); last exact: obsf_ge0.
        by move: (support t); rewrite /mask pt.
    have Le := wp_mono (denote c) Hmono s.
    by rewrite Emask in Le.
apply/(proj2 (valid_iff _ _ _ _))=>s; case ps: (p s).
- exact: (bound (rank s).+1 s ps (ltnSn (rank s))).
- apply: (le_trans (y := (0 : 'End(Hq)))); last exact: obsf_ge0.
  by move: (support s); rewrite /mask ps.
Qed.

Theorem valid_integer_while (P : assertion) (p : pred cmem)
    (rank : cmem -> int) b c :
  semantic_le P (mask p semantic_top) ->
  (forall s, p s -> 0 <= rank s) ->
  CQHoare.valid true (mask (eval b) P) c P ->
  (forall k : int, CQHoare.valid true
    (mask (fun s => eval b s && p s && (rank s == k)) semantic_top) c
    (mask (fun s => rank s < k) semantic_top)) ->
  CQHoare.valid true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>support nonneg inv decrease.
apply: (@valid_classical_while P p (fun s => absz (rank s)) b c support inv)=>k.
apply: (@CQHoare.valid_consequence true
  (mask (fun s => eval b s && p s && (rank s == Posz k)) semantic_top)
  (mask (fun s => rank s < Posz k) semantic_top) _ _ c).
- move=>s; rewrite /mask.
  case E: (eval b s && p s && (absz (rank s) == k)); last exact: obsf_ge0.
  have /andP[/andP[bs ps] /eqP rk] := E.
  have Rk : rank s = Posz k by rewrite -(gez0_abs (nonneg s ps)) rk.
  by rewrite bs ps Rk eqxx.
- move=>s; rewrite /mask; case E: (rank s < Posz k); last exact: obsf_ge0.
  case ps: (p s)=>/=; last by [].
  have L : (absz (rank s) < k)%N.
    by rewrite -ltz_nat (gez0_abs (nonneg s ps)).
  by rewrite L.
- exact: decrease.
Qed.

Theorem derives_integer_while (P : assertion) (p : pred cmem)
    (rank : cmem -> int) b c :
  semantic_le P (mask p semantic_top) ->
  (forall s, p s -> 0 <= rank s) ->
  derives true (mask (eval b) P) c P ->
  (forall k : int, derives true
    (mask (fun s => eval b s && p s && (rank s == k)) semantic_top) c
    (mask (fun s => rank s < k) semantic_top)) ->
  derives true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>support nonneg /derives_sound inv decrease; apply: derives_complete.
apply: valid_integer_while support nonneg inv _ =>k.
exact: derives_sound (decrease k).
Qed.
End CQClassicalRanking.


Module CQQuantumFrame.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


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
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage.
Import Summable_Reindex.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma sum_commute (I : choiceType) (f : I -> 'SO(Hq)) E :
  summable f -> (forall i, f i :o E = E :o f i) ->
  sum f :o E = E :o sum f.
Proof.
move=>Hsum Hcomm.
have Hcv := norm_bounded_cvg Hsum.
rewrite (cvg_linearP_sum (x := f) (f := fun F => F :o E) (linear_compr_so E) Hcv)
  (cvg_linearP_sum (x := f) (f := fun F => E :o F) (linear_comp_so E) Hcv).
by apply: eq_sum=>i; apply: Hcomm.
Qed.

Lemma slet_commute (K L : kernel) E :
  (forall i j, K i j :o E = E :o K i j) ->
  (forall i j, L i j :o E = E :o L i j) ->
  forall i j, slet K L i j :o E = E :o slet K L i j.
Proof.
move=>HK HL i j; change (sum (fun k => L k j :o K i k) :o E =
  E :o sum (fun k => L k j :o K i k)).
apply: sum_commute; first exact: CQKernel.composition_kernel_summable.
by move=>k; rewrite -comp_soA HK comp_soA HL -comp_soA.
Qed.

Lemma sdlet_commute (T : choiceType) (f : cmem -> T -> cmem)
  (g : cmem -> {vdistr T -> 'SO(Hq)}) E :
  (forall i k, g i k :o E = E :o g i k) ->
  forall i j, sdlet f g i j :o E = E :o sdlet f g i j.
Proof.
move=>Hg i j; change (sum (fun k => sunit_def (f i k) (g i k : 'SO(Hq)) j) :o E =
  E :o sum (fun k => sunit_def (f i k) (g i k : 'SO(Hq)) j)).
apply: sum_commute; first exact: (@filtered_row_summable _ _ _ _ f g i j).
by move=>k; rewrite /sunit_def; case: ifP=>_; rewrite ?comp_so0l ?comp_so0r // Hg.
Qed.

Lemma while_commute b (K : kernel) E :
  (forall i j, K i j :o E = E :o K i j) ->
  forall i j, while_sem b K i j :o E = E :o while_sem b K i j.
Proof.
move=>HK.
have HI n : forall i j, while_sem_iter b K n i j :o E = E :o while_sem_iter b K n i j.
  elim: n=>[|n IH] i j /=.
  - by rewrite abort_semE comp_so0l comp_so0r.
  - case: (esem b i).
    + exact: (@slet_commute K (while_sem_iter b K n) E HK IH i j).
    + by rewrite skip_semE; case: ifP=>_; rewrite ?comp_so1l ?comp_so1r ?comp_so0l ?comp_so0r.
move=>i j.
have Hcv : cvgn (fun n => while_sem_iter b K n i j).
  apply: summableE_is_cvg; exact: while_sem_is_cvg.
rewrite -while_sem_limEE -so_comp_liml // -so_comp_limr //.
by apply: eq_lim=>n; apply: HI.
Qed.

Lemma denote_support_commute c (S : {set mlab}) (E : 'SO(Hq)) :
  quantum_variables c :<=: S ->
  (forall T (F : 'SO_T), T :<=: S -> liftfso F :o E = E :o liftfso F) ->
  forall i j, denote c i j :o E = E :o denote c i j.
Proof.
elim: c=>[| |t x e|t x p|t u x q M|u q phi|u q U|
  c IHc d IHd|b c IHc d IHd|b c IHc] Hsub Hlocal i j /=.
- by rewrite skip_semE; case: ifP=>_; rewrite ?comp_so1l ?comp_so1r ?comp_so0l ?comp_so0r.
- by rewrite abort_semE comp_so0l comp_so0r.
- rewrite /assign_sem /sunit /sunit_vdistr /sunit_def /=.
  by case: ifP=>_; rewrite ?comp_so1l ?comp_so1r ?comp_so0l ?comp_so0r.
- apply: (@sdlet_commute (eval_ctype t)
    (fun (s : cmem) (k : eval_ctype t) => (s.[x <- k])%M)
    (fun s => sdistr Hq (esem (probability_expression p) s)) E _ i j)=>s k.
  by rewrite /sdistr /sdistr_def comp_soZl comp_soZr comp_so1l comp_so1r.
- apply: (@sdlet_commute (eval_qtype t)
    (fun (s : cmem) (k : eval_qtype t) => (s.[x <- k])%M)
    (fun s => measurement_branches q M s) E _ i j)=>s k.
  change (measurement_branches q M s k :o E = E :o measurement_branches q M s k).
  rewrite measurement_branchE; exact: Hlocal Hsub.
- rewrite /initial_sem /sunit /sunit_vdistr /sunit_def /=.
  case: ifP=>_; last by rewrite comp_so0l comp_so0r.
  exact: Hlocal Hsub.
- rewrite /unitary_sem /sunit /sunit_vdistr /sunit_def /=.
  case: ifP=>_; last by rewrite comp_so0l comp_so0r.
  exact: Hlocal Hsub.
- apply: slet_commute.
  + apply: IHc Hlocal; exact: fintype.subset_trans (finset.subsetUl _ _) Hsub.
  + apply: IHd Hlocal; exact: fintype.subset_trans (finset.subsetUr _ _) Hsub.
- case: (esem b i).
  + exact: (IHc (fintype.subset_trans (finset.subsetUl _ _) Hsub) Hlocal i j).
  + exact: (IHd (fintype.subset_trans (finset.subsetUr _ _) Hsub) Hlocal i j).
- apply: while_commute; exact: IHc Hsub Hlocal.
Qed.

Lemma denote_disjoint_commute c S (F : 'SO[msys]_S) :
  [disjoint quantum_variables c & S] -> forall i j,
  denote c i j :o liftfso F = liftfso F :o denote c i j.
Proof.
move=>Hdis; apply: (@denote_support_commute c (quantum_variables c) (liftfso F))=>//.
move=>T G Hsub; apply: liftfso_compC.
exact: fintype.disjointWl Hsub Hdis.
Qed.

Lemma dual_denote_disjoint_commute c S (F : 'SO[msys]_S) :
  [disjoint quantum_variables c & S] -> forall i j,
  (denote c i j)^*o :o liftfso F = liftfso F :o (denote c i j)^*o.
Proof.
move=>Hdis i j.
have E := congr1 (fun E : 'SO(Hq) => E^*o)
  (@denote_disjoint_commute c S F^*o Hdis i j).
by rewrite !dualso_comp !liftfso_dual dualsoK in E; symmetry.
Qed.

Lemma wp_external c S (F : 'SO[msys]_S) (Q R : assertion) :
  [disjoint quantum_variables c & S] ->
  (forall s, (R s : 'End(Hq)) = liftfso F (Q s)) -> forall s,
  (wp (denote c) R s : 'End(Hq)) = liftfso F (wp (denote c) Q s).
Proof.
move=>Hdis HR s; rewrite !wpE.
have Hcv := norm_bounded_cvg (term_summable (denote c) Q s).
rewrite (cvg_linearP_sum (x := fun t => (denote c s t)^*o (Q t))
  (f := liftfso F) (superop_is_linear (liftfso F)) Hcv).
apply: eq_sum=>t; rewrite HR.
have E := congr1 (fun E : 'SO(Hq) => E (Q t))
  (@dual_denote_disjoint_commute c S F Hdis s t).
by rewrite !comp_soE in E.
Qed.

Definition image S (F : 'DQO[msys]_S) (Q : assertion) : assertion :=
  fun s => ObsLf_Build (dqo_obslf (liftfso F) (Q s)).

Lemma imageE S (F : 'DQO[msys]_S) Q s : (image F Q s : 'End(Hq)) = liftfso F (Q s).
Proof. by []. Qed.

Lemma wp_image c S (F : 'DQO[msys]_S) Q :
  [disjoint quantum_variables c & S] -> forall s,
  (wp (denote c) (image F Q) s : 'End(Hq)) = liftfso F (wp (denote c) Q s).
Proof. move=>Hdis; exact: wp_external Hdis (imageE F Q). Qed.

Lemma lift_identity S (F : 'SO[msys]_S) : liftfso F \1 = liftf_lf (F \1).
Proof. by rewrite -{1}(@liftf_lf1 _ msys S) liftfsoEf. Qed.

Lemma subunital_completion S (F : 'DQO[msys]_S) :
  exists G : 'CP[msys]_S, ((F : 'SO[msys]_S) + (G : 'SO[msys]_S)) \1 = \1.
Proof.
have HP : 0%:VF ⊑ \1 - F \1 by rewrite subv_ge0; exact: dqo1_le1.
have [g Hg] := gef0_form HP.
exists (formso g); by rewrite add_soE formsoE comp_lfun1r -Hg addrC subrK.
Qed.

Lemma loss_unital c S (F : 'SO[msys]_S) s :
  [disjoint quantum_variables c & S] -> F \1 = \1 ->
  liftfso F (\1 - (wp (denote c) semantic_top s : 'End(Hq))) =
    \1 - (wp (denote c) semantic_top s : 'End(Hq)).
Proof.
move=>Hdis HF.
have Htop : forall t : cmem, (semantic_top t : 'End(Hq)) = liftfso F (semantic_top t).
  by move=>t; rewrite /semantic_top /= lift_identity HF liftf_lf1.
have HW := @wp_external c S F semantic_top semantic_top Hdis Htop s.
by rewrite linearB /= lift_identity HF liftf_lf1 -HW.
Qed.

Lemma loss_subunital c S (F : 'DQO[msys]_S) s :
  [disjoint quantum_variables c & S] ->
  liftfso F (\1 - (wp (denote c) semantic_top s : 'End(Hq))) ⊑
    \1 - (wp (denote c) semantic_top s : 'End(Hq)).
Proof.
move=>Hdis; have [G HG] := subunital_completion F.
have E := @loss_unital c S ((F : 'SO[msys]_S) + (G : 'SO[msys]_S)) s Hdis HG.
have Emap : liftfso ((F : 'SO[msys]_S) + (G : 'SO[msys]_S)) =
    liftfso F + liftfso G by rewrite /liftfso linearD.
rewrite Emap add_soE in E.
rewrite -{2}E levDl; apply: cp_ge0.
by rewrite subv_ge0; exact: obsf_le1.
Qed.

Lemma wlp_decompose (K : kernel) Q s :
  (wlp K Q s : 'End(Hq)) =
    (\1 - (wp K semantic_top s : 'End(Hq))) + (wp K Q s : 'End(Hq)).
Proof.
change (\1 - (wp K (complement Q) s : 'End(Hq)) =
  (\1 - (wp K semantic_top s : 'End(Hq))) + (wp K Q s : 'End(Hq))).
rewrite (@wp_difference _ _ _ K semantic_top Q (complement Q)) //.
by rewrite opprB addrA addrAC.
Qed.

Lemma pre_image_le total c S (F : 'DQO[msys]_S) Q s :
  [disjoint quantum_variables c & S] ->
  liftfso F (pre total c Q s) ⊑ (pre total c (image F Q) s : 'End(Hq)).
Proof.
move=>Hdis; case: total.
- by change (liftfso F (wp (denote c) Q s) ⊑ (wp (denote c) (image F Q) s : 'End(Hq)));
    rewrite wp_image.
- change (liftfso F (wlp (denote c) Q s) ⊑ (wlp (denote c) (image F Q) s : 'End(Hq))).
  rewrite !wlp_decompose linearD wp_image // levD2r.
  exact: loss_subunital Hdis.
Qed.

Lemma valid_supoper total P c Q S (F : 'DQO[msys]_S) :
  [disjoint quantum_variables c & S] -> CQHoare.valid total P c Q ->
  CQHoare.valid total (image F P) c (image F Q).
Proof.
move=>Hdis /(proj1 (valid_iff _ _ _ _)) V.
apply/(proj2 (valid_iff _ _ _ _))=>s.
apply: (le_trans _ (@pre_image_le total c S F Q s Hdis)).
exact: cp_preserve_order (V s).
Qed.

Lemma derives_supoper total P c Q S (F : 'DQO[msys]_S) :
  [disjoint quantum_variables c & S] -> derives total P c Q ->
  derives total (image F P) c (image F Q).
Proof.
move=>Hdis /derives_sound V; apply: derives_complete.
exact: valid_supoper Hdis V.
Qed.
End CQQuantumFrame.


Module CQParameterizedCounterexample.
(* A counterexample to classical.pdf Lemma 4.15(3), partial mode.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage CQAssertion CQPredicate CQParameterized.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma selector_list_none_partial (I : finType) (choose : expression (option I))
    (branch : I -> command) indices m (Q : assertion) :
  eval choose m = None ->
  CQHoare.pre false (selector_list choose branch indices) Q m = \1.
Proof.
move=>He; elim: indices=>[|i rest IH].
- by rewrite /selector_list /CQHoare.pre /xp /= wlp_abort.
- change (CQHoare.pre false
    (Conditional (selector_guard choose i) (branch i)
      (selector_list choose branch rest)) Q m = \1).
  by rewrite CQHoare.pre_conditional /conditional /selector_guard /eval /=
    -/(eval choose m) He.
Qed.

Theorem parameterized_zero_partial t K (q : wf_qreg t)
    (U : 'I_K -> 'FU('Ht t)) (Q : assertion) m :
  CQHoare.pre false (parameterized_unitary q U (EConst (0 : int))) Q m = \1.
Proof. apply: selector_list_none_partial; exact: parameter_selector_zero. Qed.

Theorem parameterized_zero_printed t K (q : wf_qreg t)
    (U : 'I_K -> 'FU('Ht t)) (Q : assertion) m :
  parameterized_pre q U (EConst (0 : int)) Q m = 0%:VF.
Proof. by rewrite /parameterized_pre /selector_pre parameter_selector_zero. Qed.

Theorem parameterized_zero_counterexample t K (q : wf_qreg t)
    (U : 'I_K -> 'FU('Ht t)) (Q : assertion) m :
  CQHoare.pre false (parameterized_unitary q U (EConst (0 : int))) Q m !=
    parameterized_pre q U (EConst (0 : int)) Q m.
Proof.
rewrite parameterized_zero_partial parameterized_zero_printed.
apply/negP=>/eqP E.
have H := congr1 (fun A : 'FO(Hq) => (A : 'End(Hq))) E.
by move/eqP: H; rewrite /= oner_eq0.
Qed.
End CQParameterizedCounterexample.


Module CQProbabilisticPure.
(* Probabilistic composition via saturated projector support. See PROOF_NOTES.md. *)


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
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQProbabilisticComposition.
Local Open Scope hspace_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation C := hermitian.C.

Definition register_effect u (q : wf_qreg u) (M : 'FO('Ht u)) : 'FO(Hq) :=
  [obs of liftf_lf (tf2f q q M)].
Definition register_pure u (q : wf_qreg u) (v : 'NS('Ht u)) : {hspace Hq} :=
  HSType [proj of liftf_lf (tf2f q q [> v; v <])].

Lemma pure_sandwich (H : chsType) (v : 'NS(H)) (M : 'End(H)) :
  [> (v : H); (v : H) <] \o M \o [> (v : H); (v : H) <] = [< (v : H); M (v : H) >] *: [> (v : H); (v : H) <].
Proof. by rewrite outp_compl outp_comp adj_dotEl. Qed.

Lemma register_pure_sandwich u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u)) :
  register_pure q v \o register_effect q M \o register_pure q v =
  [< (v : 'Ht u); M (v : 'Ht u) >] *: (register_pure q v : 'End(Hq)).
Proof.
rewrite /register_pure /register_effect !hsE /= -!liftf_lf_comp !tf2f_comp.
by rewrite pure_sandwich !linearZ.
Qed.

Definition pure_success_effect u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u)) : 'FO(Hq) :=
  register_effect q [obs of (initialso v)^*o M].

Lemma pure_success_effectE u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u)) :
  (pure_success_effect q v M : 'End(Hq)) = [< (v : 'Ht u); M (v : 'Ht u) >] *: \1.
Proof.
by rewrite /pure_success_effect /register_effect /= dualso_initialE
  !linearZ /= tf2f1 liftf_lf1.
Qed.

Lemma masked_projection (p : pred cmem) (P : {hspace Hq}) :
  projection_assertion (fun s => if p s then P else `0`) =
  mask p (fun _ => [obs of P]).
Proof.
apply/funext=>s; apply/val_inj; rewrite /projection_assertion /mask /=.
by case: (p s); rewrite // hs2lf0E.
Qed.

Theorem valid_probcomp u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u))
    (p' p : pred cmem) c d (Q : assertion) :
  CQHoare.valid true (mask p' semantic_top) c
    (mask p (fun _ => [obs of register_pure q v])) ->
  CQHoare.valid true (mask p (fun _ => register_effect q M)) d Q ->
  CQHoare.valid true (mask p' (fun _ => pure_success_effect q v M)) (Sequence c d) Q.
Proof.
move=>Vc Vd.
apply: (@valid_probcomp_projection p'
  (fun s => if p s then register_pure q v else `0`)
  (mask p (fun _ => register_effect q M))
  (mask p' (fun _ => pure_success_effect q v M)) Q
  ([< (v : 'Ht u); M (v : 'Ht u) >]) c d).
- move=>s; rewrite /mask; by case: (p' s); rewrite // pure_success_effectE.
- move=>s; rewrite /mask; case: (p s); first exact: register_pure_sandwich.
  by rewrite hs2lf0E comp_lfun0l comp_lfun0r scaler0.
- by rewrite masked_projection.
- exact: Vd.
Qed.

Theorem derives_probcomp u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u))
    (p' p : pred cmem) c d (Q : assertion) :
  derives true (mask p' semantic_top) c
    (mask p (fun _ => [obs of register_pure q v])) ->
  derives true (mask p (fun _ => register_effect q M)) d Q ->
  derives true (mask p' (fun _ => pure_success_effect q v M)) (Sequence c d) Q.
Proof.
move=>/derives_sound Vc /derives_sound Vd; apply: derives_complete.
exact: valid_probcomp Vc Vd.
Qed.
End CQProbabilisticPure.


Module CQGhostRanking.
(* Fresh integer ghosts and the paper's C-WhileT rule. See PROOF_NOTES.md. *)


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
Import CQAssertion CQPredicate CQHoare ClassicalLanguage ClassicalFootprint CQAssertionLocality.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma writes_variables c k : k \in writes c -> variables c k.
Proof.
elim: c=>[| |u x e|u x p|u v x q M|u q phi|u q U|
    c IH d IHd|b c IH d IHd|b c IH] /=; rewrite ?in_nil //.
- by rewrite inE=>/eqP E; left; exact E.
- by rewrite inE=>/eqP E; left; exact E.
- by rewrite inE=>/eqP E; left; exact E.
- rewrite mem_cat=>/orP[H|H]; [left; exact: IH|right; exact: IHd].
- rewrite mem_cat=>/orP[H|H]; right; [left; exact: IH|right; exact: IHd].
- by move=>H; right; exact: IH.
Qed.

Theorem valid_fresh_integer_while (P : assertion) (p b : bool_expr)
    (r : expression int) (z : variable Integer) c X :
  (variables c `<=` X)%classic ->
  (expression_variables b `<=` X)%classic ->
  (expression_variables p `<=` X)%classic ->
  (expression_variables r `<=` X)%classic -> ~ X (key z) ->
  semantic_le P (mask (eval p) semantic_top) ->
  (forall s, eval p s -> 0 <= eval r s) ->
  CQHoare.valid true (mask (eval b) P) c P ->
  CQHoare.valid true
    (mask (fun s => eval b s && eval p s && (eval r s == (s.[z])%M)) semantic_top) c
    (mask (fun s => eval r s < (s.[z])%M) semantic_top) ->
  CQHoare.valid true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>Hc Hb Hp Hr Hz support nonneg inv dec.
apply: (@CQClassicalRanking.valid_integer_while P (eval p) (eval r) b c
  support nonneg inv)=>k.
pose g : bool_expr := EApp (EConst (fun v : int => v == k)) (EVar z).
have Hg : forall j, expression_variables g j -> j \notin writes c.
  move=>j; rewrite /g /EApp /EConst /EVar /=; move=>[[]|E].
  apply/negP=>Hj; apply: Hz; apply: Hc.
  by rewrite -E; exact: writes_variables Hj.
have Vg := CQInvariant.valid_invariant Hg dec.
pose pk := fun s => eval b s && eval p s && (eval r s == k) && ((s.[z])%M == k).
pose Qk : assertion := mask (fun s => eval r s < k) semantic_top.
have Vk : CQHoare.valid true (mask pk semantic_top) c Qk.
  apply: (@CQHoare.valid_consequence true _ _ _ _ c _ _ Vg).
  - move=>s; rewrite /mask /pk /g /eval /=.
    case E: (esem b s && esem p s && (esem r s == k) && (s.[z]%M == k));
      last exact: obsf_ge0.
    have /andP[/andP[/andP[bs ps] /eqP rk] /eqP zk] := E.
    by rewrite bs ps rk zk eqxx.
  - move=>s; rewrite /Qk /mask /g /eval /=.
    case Z: (s.[z]%M == k); last exact: obsf_ge0.
    by rewrite (eqP Z).
have Qlocal : assertion_local X Qk.
  move=>s t Hst; by rewrite /Qk /mask (eval_agree Hr Hst).
have Ve := @valid_exist true Integer z pk (\1 : 'FO(Hq)) c Qk X Hc Hz Qlocal Vk.
apply: (@CQHoare.valid_consequence true _ _ _ _ c _ (semantic_le_refl Qk) Ve).
move=>s; rewrite /mask.
case E: (eval b s && eval p s && (eval r s == k)); last exact: obsf_ge0.
have Hw : exists_update z pk s.
  apply/asboolP; exists k.
  have Hst := @agree_on_external X Integer z k s Hz.
  by rewrite /pk -(eval_agree Hb Hst) -(eval_agree Hp Hst)
    -(eval_agree Hr Hst) get_set_eq E eqxx.
by rewrite Hw.
Qed.

Theorem derives_fresh_integer_while (P : assertion) (p b : bool_expr)
    (r : expression int) (z : variable Integer) c X :
  (variables c `<=` X)%classic ->
  (expression_variables b `<=` X)%classic ->
  (expression_variables p `<=` X)%classic ->
  (expression_variables r `<=` X)%classic -> ~ X (key z) ->
  semantic_le P (mask (eval p) semantic_top) ->
  (forall s, eval p s -> 0 <= eval r s) ->
  derives true (mask (eval b) P) c P ->
  derives true
    (mask (fun s => eval b s && eval p s && (eval r s == (s.[z])%M)) semantic_top) c
    (mask (fun s => eval r s < (s.[z])%M) semantic_top) ->
  derives true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>Hc Hb Hp Hr Hz support nonneg /derives_sound inv /derives_sound dec.
apply: derives_complete; exact: valid_fresh_integer_while Hc Hb Hp Hr Hz support nonneg inv dec.
Qed.
End CQGhostRanking.


Module CQQuantumSelector.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


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
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition selector (U : chsType) (I : finType) (w : I -> C) (v : I -> U) :=
  \sum_i w i *: (initialso (v i))^*o.

Lemma selectorE (U : chsType) (I : finType) w (v : I -> U) A :
  selector w v A = (\sum_i w i * [<v i; A (v i)>]) *: \1.
Proof.
rewrite /selector sum_soE scaler_suml.
by apply:eq_bigr=>i _; rewrite scale_soE dualso_initialE scalerA.
Qed.

Lemma selector_cp (U : chsType) (I : finType) w (v : I -> U) :
  (forall i, 0 <= w i) -> selector w v \is cpmap.
Proof.
move=>Hw; rewrite -geso0_cpE /selector; apply: sumv_ge0=>i _.
apply: scalev_ge0; first exact: Hw.
by rewrite geso0_cpE is_cpmap.
Qed.

Lemma selector_dqo (U : chsType) (I : finType) w (v : I -> U) :
  (forall i, 0 <= w i) -> (\sum_i w i <= 1) ->
  (forall i, [<v i; v i>] = 1) -> (selector w v)^*o \is cptn.
Proof.
move=>Hw Hsum Hv; rewrite (CPMap_BuildE (selector_cp v Hw)) cp_isdqoE.
change (selector w v \1 ⊑ \1).
rewrite selectorE; under eq_bigr do rewrite id_lfunE Hv mulr1.
rewrite -{2}(scale1r (\1 : 'End(U))); apply: lev_wpscale2r=>//.
exact: (obsf_ge0 (\1 : 'FO(U))).
Qed.

Lemma selector_outp (U : chsType) (I : finType) w (v : I -> U) j :
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  selector w v [>v j; v j<] = w j *: \1.
Proof.
move=>Hv; rewrite selectorE.
under eq_bigr=>i _ do rewrite outpE dotpZr !Hv.
rewrite (bigD1 j) //= eqxx !mulr1 big1 ?addr0 // =>i Hij.
by rewrite eq_sym (negbTE Hij) !mulr0.
Qed.

Lemma selector_labeled S T (I : finType) w (v : I -> 'H[msys]_T)
    (X : I -> 'F[msys]_S) :
  [disjoint S & T] ->
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  liftfso (selector w v)
    (\sum_i (liftf_lf (X i) \o liftf_lf [>v i; v i<])) =
    \sum_i w i *: liftf_lf (X i).
Proof.
move=>Hdis Hv; rewrite linear_sum /=; apply:eq_bigr=>i _.
rewrite liftfsoEf_compl // liftfsoEf selector_outp //.
by rewrite linearZ /= liftf_lf1 -comp_lfunZr comp_lfun1r.
Qed.

Theorem derives_lsum total c S T (I : finType) (w : I -> C)
    (v : I -> 'H[msys]_T) (P Q : I -> cmem -> 'F[msys]_S)
    (A B R R' : assertion) :
  [disjoint S & T] -> [disjoint quantum_variables c & T] ->
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  (forall i, 0 <= w i) -> (\sum_i w i <= 1) ->
  (forall s, (A s : 'End(Hq)) =
    \sum_i (liftf_lf (P i s) \o liftf_lf [>v i; v i<])) ->
  (forall s, (B s : 'End(Hq)) =
    \sum_i (liftf_lf (Q i s) \o liftf_lf [>v i; v i<])) ->
  (forall s, (R s : 'End(Hq)) = \sum_i w i *: liftf_lf (P i s)) ->
  (forall s, (R' s : 'End(Hq)) = \sum_i w i *: liftf_lf (Q i s)) ->
  derives total A c B -> derives total R c R'.
Proof.
move=>Hdis Hc Hv Hw Hsum HA HB HR HR' Hder.
have Hnorm i : [<v i; v i>] = 1 by rewrite Hv eqxx.
pose F := DualQO_Build (selector_dqo Hw Hsum Hnorm).
have ER : image F A = R.
  apply/funext=>s; apply/val_inj.
  change (liftfso (selector w v) (A s) = (R s : 'End(Hq))).
  by rewrite HA selector_labeled // HR.
have ER' : image F B = R'.
  apply/funext=>s; apply/val_inj.
  change (liftfso (selector w v) (B s) = (R' s : 'End(Hq))).
  by rewrite HB selector_labeled // HR'.
rewrite -ER -ER'; exact: derives_supoper Hc Hder.
Qed.
End CQQuantumSelector.


Module CQQuantumSpaceRules.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


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
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition lifted S (P : cmem -> 'FO[msys]_S) : assertion :=
  fun s => liftf_lf (P s).

Lemma effect_map_exists (U : chsType) (M : 'FO(U)) :
  exists F : 'DQO(U), F \1 = M.
Proof.
have [B HB] := gef0_form (obsf_ge0 M).
have H1 : (formso B : 'CP(U)) \1 ⊑ \1.
  by rewrite formsoE comp_lfun1r -HB; exact: obsf_le1.
have Hcp : (formso B)^*o \is cptn := (introT (cp_isdqoP (formso B)) H1).
exists (DualQO_Build Hcp).
by change (formso B \1 = M); rewrite formsoE comp_lfun1r -HB.
Qed.

Lemma lift_tensor_image S T (F : 'SO[msys]_T) (X : 'F[msys]_S) :
  [disjoint S & T] ->
  liftfso F (liftf_lf X) = liftf_lf (X \⊗ F \1).
Proof.
move=>Hdis.
rewrite -{1}(comp_lfun1r (liftf_lf X)) liftfsoEf_compl //.
by rewrite lift_identity liftf_lf_compT.
Qed.

Theorem derives_tens total c S T (P Q : cmem -> 'FO[msys]_S)
    (M : 'FO[msys]_T) (R R' : assertion) :
  [disjoint S & T] -> [disjoint quantum_variables c & T] ->
  (forall s, (R s : 'End(Hq)) = liftf_lf ((P s : 'F[msys]_S) \⊗ M)) ->
  (forall s, (R' s : 'End(Hq)) = liftf_lf ((Q s : 'F[msys]_S) \⊗ M)) ->
  derives total (lifted P) c (lifted Q) -> derives total R c R'.
Proof.
move=>Hdis Hc HR HR' Hder; have [F HF] := effect_map_exists M.
have ER : image F (lifted P) = R.
  apply/funext=>s; apply/val_inj; change (liftfso F (liftf_lf (P s)) = (R s : 'End(Hq))).
  by rewrite lift_tensor_image // HF HR.
have ER' : image F (lifted Q) = R'.
  apply/funext=>s; apply/val_inj; change (liftfso F (liftf_lf (Q s)) = (R' s : 'End(Hq))).
  by rewrite lift_tensor_image // HF HR'.
rewrite -ER -ER'; exact: derives_supoper Hc Hder.
Qed.

Lemma tensor_effect S T (M : 'FO[msys]_S) (N : 'FO[msys]_T) :
  [disjoint S & T] -> (M : 'F[msys]_S) \⊗ (N : 'F[msys]_T) \is obslf.
Proof.
move=>Hdis; apply/obslf_lefP; split.
- exact: tenf_ge0 Hdis (obsf_ge0 M) (obsf_ge0 N).
- apply: (le_trans (y := (\1 : 'F[msys]_S) \⊗ (N : 'F[msys]_T))).
  + rewrite -subv_ge0 -linearBl /=; apply: tenf_ge0 Hdis _ (obsf_ge0 N).
    by rewrite subv_ge0; exact: obsf_le1.
  + rewrite -(@tenf11 _ msys S T).
    rewrite -subv_ge0 -linearBr /=; apply: tenf_ge0 Hdis (obsf_ge0 (\1 : 'FO[msys]_S)) _.
    by rewrite subv_ge0; exact: obsf_le1.
Qed.

Definition tens (S T : {set mlab}) (Hdis : [disjoint S & T]) (P : cmem -> 'FO[msys]_S)
    (M : 'FO[msys]_T) : assertion :=
  fun s => liftf_lf (ObsLf_Build (tensor_effect (P s) M Hdis)).

Corollary derives_tens_direct total c (S T : {set mlab}) (Hdis : [disjoint S & T])
    (P Q : cmem -> 'FO[msys]_S) (M : 'FO[msys]_T) :
  [disjoint quantum_variables c & T] ->
  derives total (lifted P) c (lifted Q) ->
  derives total (tens Hdis P M) c (tens Hdis Q M).
Proof.
move=>Hc Hder; exact: (@derives_tens total c S T P Q M
  (tens Hdis P M) (tens Hdis Q M) Hdis Hc (fun _ => erefl) (fun _ => erefl) Hder).
Qed.
End CQQuantumSpaceRules.


Module CQQuantumSuperposition.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


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
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame CQAssertionAlgebra.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition selecting_vector (U : chsType) (I : finType) (a : I -> C) (v : I -> U) :=
  \sum_i (a i)^* *: v i.

Lemma selecting_overlap (U : chsType) (I : finType) a (v : I -> U) j :
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  [<selecting_vector a v; v j>] = a j.
Proof.
move=>Hv; rewrite /selecting_vector dotp_suml (bigD1 j) //=.
rewrite dotpZl Hv eqxx conjCK mulr1 big1 ?addr0 // =>i Hij.
by rewrite dotpZl Hv (negbTE Hij) mulr0.
Qed.

Lemma selecting_norm (U : chsType) (I : finType) a (v : I -> U) :
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  (\sum_i a i * (a i)^* = 1) ->
  [<selecting_vector a v; selecting_vector a v>] = 1.
Proof.
move=>Hv Ha; rewrite {2}/selecting_vector dotp_sumr.
under eq_bigr=>i _ do rewrite dotpZr selecting_overlap // mulrC.
exact: Ha.
Qed.

Lemma unit_selector_dqo (U : chsType) (u : U) :
  [<u;u>] = 1 -> ((initialso u)^*o)^*o \is cptn.
Proof.
move=>Hu; rewrite cp_isdqoE dualso_initialE id_lfunE Hu scale1r.
exact: lexx.
Qed.

Lemma selected_outp (U : chsType) (I : finType) a (v : I -> U) i j :
  (forall i j, [<v i;v j>] = (i == j)%:R) ->
  (initialso (selecting_vector a v))^*o [>v i;v j<] =
    (a i * (a j)^*) *: \1.
Proof.
move=>Hv; rewrite dualso_initialE outpE dotpZr selecting_overlap //.
by rewrite -conj_dotp selecting_overlap // mulrC.
Qed.

Lemma selected_entangled S T (I : finType) a (v : I -> 'H[msys]_T)
    (phi : I -> 'H[msys]_S) :
  [disjoint S & T] ->
  (forall i j, [<v i;v j>] = (i == j)%:R) ->
  liftfso (initialso (selecting_vector a v))^*o
    (liftf_lf [>\sum_i tenv (phi i) (v i); \sum_i tenv (phi i) (v i)<]) =
  liftf_lf [>\sum_i a i *: phi i; \sum_i a i *: phi i<].
Proof.
move=>Hdis Hv; rewrite !outp_suml !linear_sum /=.
apply:eq_bigr=>i _; rewrite !outp_sumr !linear_sum /=.
apply:eq_bigr=>j _.
rewrite -tenf_outp -liftf_lf_compT // liftfsoEf_compl // liftfsoEf selected_outp //.
by rewrite outpZl outpZr !linearZ /= liftf_lf1 comp_lfun1r scalerA.
Qed.

Lemma expect_scaled (A B : assertion) r rho :
  (forall s, (A s : 'End(Hq)) = r *: (B s : 'End(Hq))) ->
  expect A rho = r * expect B rho.
Proof.
move=>HE.
pose terms := Summable.build (expect_summable B rho).
have TE : expect_term A rho = r *: terms.
  apply/funext=>s; change (\Tr (A s \o rho s) = r * \Tr (B s \o rho s)).
  by rewrite HE linearZl /= linearZ.
by rewrite /expect TE summable_sumZ.
Qed.

Theorem derives_suppos c S T (I : finType) (a : I -> C)
    (v : I -> 'H[msys]_T) (phi psi : I -> 'H[msys]_S)
    (p q : pred cmem) r (A B R R' : assertion) :
  [disjoint S & T] -> [disjoint quantum_variables c & T] ->
  (forall i j, [<v i;v j>] = (i == j)%:R) ->
  (\sum_i a i * (a i)^* = 1) -> 0 < r ->
  (forall s, (A s : 'End(Hq)) = r *:
    (if p s then liftf_lf [>\sum_i tenv (phi i) (v i); \sum_i tenv (phi i) (v i)<] else 0)) ->
  (forall s, (B s : 'End(Hq)) = r *:
    (if q s then liftf_lf [>\sum_i tenv (psi i) (v i); \sum_i tenv (psi i) (v i)<] else 0)) ->
  (forall s, (R s : 'End(Hq)) =
    if p s then liftf_lf [>\sum_i a i *: phi i; \sum_i a i *: phi i<] else 0) ->
  (forall s, (R' s : 'End(Hq)) =
    if q s then liftf_lf [>\sum_i a i *: psi i; \sum_i a i *: psi i<] else 0) ->
  derives true A c B -> derives true R c R'.
Proof.
move=>Hdis Hc Hv Ha Hr HA HB HR HR' Hder.
pose F := DualQO_Build (unit_selector_dqo (selecting_norm Hv Ha)).
have HE s : (image F A s : 'End(Hq)) = r *: (R s : 'End(Hq)).
  change (liftfso (initialso (selecting_vector a v))^*o (A s) = r *: (R s : 'End(Hq))).
  rewrite HA HR linearZ /=; case: (p s); last by rewrite linear0.
  by rewrite selected_entangled.
have HE' s : (image F B s : 'End(Hq)) = r *: (R' s : 'End(Hq)).
  change (liftfso (initialso (selecting_vector a v))^*o (B s) = r *: (R' s : 'End(Hq))).
  rewrite HB HR' linearZ /=; case: (q s); last by rewrite linear0.
  by rewrite selected_entangled.
have HD := @derives_supoper true A c B T F Hc Hder.
apply: derives_complete=>rho.
have HV : expect (image F A) rho <= expect (image F B) (CQHoare.run c rho) :=
  @derives_sound true (image F A) c (image F B) HD rho.
rewrite (expect_scaled _ HE) (expect_scaled _ HE') in HV.
by move: HV; rewrite ler_pM2l.
Qed.
End CQQuantumSuperposition.


Module CQQuantumTrace.
(* Normalized partial trace and the Trace rule, classical.pdf Table 5.
   See PROOF_NOTES.md for the matrix-unit argument. *)


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
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame CQQuantumSelector.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition uniform_weight (U : chsType) : C := ((dim U)%:R)^-1%R.
Definition depolarizer (L : finType) (H : L -> chsType) (S : {set L}) :=
  selector (fun _ : 'Idx[H]_S => uniform_weight 'H[H]_S) (@deltav L H S).

Lemma depolarizerE (L : finType) (H : L -> chsType) S (A : 'F[H]_S) :
  depolarizer H S A = uniform_weight 'H[H]_S *: (\Tr A *: \1).
Proof. by rewrite /depolarizer selectorE -mulr_sumr -onb_trlf scalerA. Qed.

Lemma depolarizer_dqo (L : finType) (H : L -> chsType) S :
  (depolarizer H S)^*o \is cptn.
Proof.
apply: selector_dqo.
- by move=>i; rewrite /uniform_weight invr_ge0 ler0n.
- rewrite sumr_const -mulr_natl idx_card /uniform_weight mulfV //.
  by rewrite gt_eqF // dim_proper_gt0.
- by move=>i; rewrite dv_dot eqxx.
Qed.

Definition depolarizing (L : finType) (H : L -> chsType) S : 'DQO[H]_S :=
  DualQO_Build (depolarizer_dqo H S).

Lemma split_lift_outp (L : finType) (H : L -> chsType) S T (i j : 'Idx[H]_S) :
  liftf_lf [>deltav i; deltav j<] =
  liftf_lf [>deltav (idxSl (castidx (esym (setID S T)) i));
             deltav (idxSl (castidx (esym (setID S T)) j))<] \o
  liftf_lf [>deltav (idxSr (castidx (esym (setID S T)) i));
             deltav (idxSr (castidx (esym (setID S T)) j))<].
Proof.
rewrite liftf_lf_compT ?disjointID // tenf_outp -!dv_split -!deltav_cast -castlf_outp.
by rewrite liftf_lf_cast.
Qed.

Lemma partial_trace_outp (L : finType) (H : L -> chsType) S T (i j : 'Idx[H]_S) :
  ptraceso T [>deltav i; deltav j<] =
  (idxSl (castidx (esym (setID S T)) j) ==
   idxSl (castidx (esym (setID S T)) i))%:R *:
  [>deltav (idxSr (castidx (esym (setID S T)) i));
    deltav (idxSr (castidx (esym (setID S T)) j))<].
Proof.
move: (disjointID S T)=>dis.
rewrite /ptraceso {1}/fun_of_superof /= lfunE /= ptraceso_fun.unlock.
transitivity (\sum_(k : 'Idx[H]_(S :&: T))
  ((idxSl (castidx (esym (setID S T)) j) == k)%:R *
   (k == idxSl (castidx (esym (setID S T)) i))%:R) *:
  [>deltav (idxSr (castidx (esym (setID S T)) i));
    deltav (idxSr (castidx (esym (setID S T)) j))<]).
- apply:eq_bigr=>k _.
  rewrite (bigD1 (idxSr (castidx (esym (setID S T)) i))) //=
    (bigD1 (idxSr (castidx (esym (setID S T)) j))) //= !big1=>[i0/negPf ni|i0/negPf ni|].
  2: rewrite big1 // =>j0 _.
  1,2,3: rewrite castlf_outp /= !deltav_cast outpE linearZ /= !dv_split
    !idxSUl // !idxSUr // !tenv_dot // !onb_dot.
  1,2: by rewrite ?ni ?[_==i0]eq_sym ?ni ?(mulr0,mul0r) scale0r.
  by rewrite !eqxx !mulr1 !addr0.
- rewrite (bigD1 (idxSl (castidx (esym (setID S T)) i))) //=
    eqxx mulr1 big1 ?addr0 // =>k /negPf Hk.
  by rewrite Hk mulr0 scale0r.
Qed.

Lemma lift_depolarizer_outp (L : finType) (H : L -> chsType) S T (i j : 'Idx[H]_S) :
  liftfso (depolarizer H (S :&: T)) (liftf_lf [>deltav i; deltav j<]) =
  uniform_weight 'H[H]_(S :&: T) *: liftf_lf (ptraceso T [>deltav i; deltav j<]).
Proof.
have Hd : [disjoint S :\: T & S :&: T] by rewrite disjoint_sym disjointID.
rewrite (@split_lift_outp L H S T i j)
  (@liftfsoEf_compr L H (S :\: T) (S :&: T) _ _ _ Hd)
  liftfsoEf depolarizerE outp_trlf dv_dot partial_trace_outp !linearZ /=
  liftf_lf1 -!comp_lfunZl comp_lfun1l.
by rewrite !scalerA mulrC.
Qed.

Lemma lift_depolarizer (L : finType) (H : L -> chsType) S T (A : 'F[H]_S) :
  liftfso (depolarizer H (S :&: T)) (liftf_lf A) =
  uniform_weight 'H[H]_(S :&: T) *: liftf_lf (ptraceso T A).
Proof.
rewrite (onb_lfun2id deltav A) !linear_sum /=.
apply:eq_bigr=>i _; rewrite !linear_sum /=.
apply:eq_bigr=>j _.
by rewrite !linearZ /= -linear_sum /= lift_depolarizer_outp.
Qed.

Definition trace_assertion T (P : assertion) : assertion :=
  image (depolarizing msys T) P.

Lemma trace_assertionE T P s : (trace_assertion T P s : 'End(Hq)) =
  uniform_weight 'H[msys]_T *: liftf_lf (ptraceso T (P s)).
Proof.
have E := @lift_depolarizer _ msys finset.setT T (P s).
rewrite finset.setTI liftf_lf_id in E.
exact: E.
Qed.

Theorem derives_trace total P c Q (T : {set mlab}) :
  [disjoint quantum_variables c & T] -> derives total P c Q ->
  derives total (trace_assertion T P) c (trace_assertion T Q).
Proof. exact: derives_supoper. Qed.
End CQQuantumTrace.


Module CQPrimitiveFrame.
(* Table-5 Init0, Unit0 and Meas0; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumSpaceRules.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma lifted_unital S T (A : 'F[msys]_S) (E : 'QU[msys]_T) :
  [disjoint S & T] -> liftfso E (liftf_lf A) = liftf_lf A.
Proof.
move=>Hdis; by rewrite lift_tensor_image // qu1_eq1 liftf_lf_tenf1r.
Qed.

Lemma initial_pre_frame total t (q : wf_qreg t) phi S
    (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] ->
  (pre total (Initialize q phi) (lifted P) m : 'End(Hq)) = liftf_lf (P m).
Proof.
move=>Hdis; rewrite /pre CQPrimitive.initial_pre liftfso_dual.
exact: lifted_unital Hdis.
Qed.

Lemma unitary_pre_frame total t (q : wf_qreg t) U S
    (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] ->
  (pre total (Unitary q U) (lifted P) m : 'End(Hq)) = liftf_lf (P m).
Proof.
move=>Hdis; rewrite /pre CQPrimitive.unitary_pre liftfso_dual.
exact: lifted_unital Hdis.
Qed.

Theorem derives_initialize_frame total t (q : wf_qreg t) phi S
    (P : cmem -> 'FO[msys]_S) :
  [disjoint S & mset q] ->
  derives total (lifted P) (Initialize q phi) (lifted P).
Proof.
move=>Hdis; apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>m.
by rewrite initial_pre_frame.
Qed.

Corollary derives_init0 total t (q : wf_qreg t) S
    (P : cmem -> 'FO[msys]_S) :
  [disjoint S & mset q] ->
  derives total (lifted P) (Initialize q (EConst (zero_state t))) (lifted P).
Proof. exact: derives_initialize_frame. Qed.

Theorem derives_unit0 total t (q : wf_qreg t) U S
    (P : cmem -> 'FO[msys]_S) :
  [disjoint S & mset q] ->
  derives total (lifted P) (Unitary q U) (lifted P).
Proof.
move=>Hdis; apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>m.
by rewrite unitary_pre_frame.
Qed.

Definition measurement_tensor t u (x : variable (QType t))
    (q : wf_qreg u) (M : mexpr (eval_qtype t) (eval_qtype u))
    S (P : cmem -> 'FO[msys]_S) m : 'End(Hq) :=
  \sum_v liftf_lf ((P (m.[x <- v])%M : 'F[msys]_S) \⊗
    ((tm2m q q (esem M m) v)^A \o tm2m q q (esem M m) v)).

Lemma measurement_pre_frame total t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] ->
  (pre total (Measure x q M) (lifted P) m : 'End(Hq)) =
    measurement_tensor x q M P m.
Proof.
move=>Hdis; rewrite /pre CQPrimitive.measurement_pre /measurement_tensor.
apply: eq_bigr=>v _; rewrite liftf_funE -liftf_lf_adj.
change (liftf_lf (tm2m q q (esem M m) v)^A \o
  liftf_lf (P (m.[x <- v])%M) \o liftf_lf (tm2m q q (esem M m) v) =
  liftf_lf ((P (m.[x <- v])%M : 'F[msys]_S) \⊗
    ((tm2m q q (esem M m) v)^A \o tm2m q q (esem M m) v))).
have Hd : [disjoint mset q & S] by rewrite disjoint_sym.
rewrite (@liftf_lf_compC _ msys (mset q) S
  (tm2m q q (esem M m) v)^A (P (m.[x <- v])%M) Hd).
by rewrite -comp_lfunA -liftf_lf_comp (liftf_lf_compT _ _ Hdis).
Qed.

Lemma measurement_tensor_effect t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] -> measurement_tensor x q M P m \is obslf.
Proof.
move=>Hdis; rewrite -(@measurement_pre_frame true t u x q M S P m Hdis).
exact: is_obslf.
Qed.

Definition meas0_assertion t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S)
    (Hdis : [disjoint S & mset q]) : assertion :=
  fun m => ObsLf_Build (@measurement_tensor_effect t u x q M S P m Hdis).

Lemma meas0_assertionE t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S)
    (Hdis : [disjoint S & mset q]) m :
  (@meas0_assertion t u x q M S P Hdis m : 'End(Hq)) =
    measurement_tensor x q M P m.
Proof. by []. Qed.

Theorem derives_meas0 total t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S)
    (Hdis : [disjoint S & mset q]) :
  derives total (@meas0_assertion t u x q M S P Hdis) (Measure x q M) (lifted P).
Proof.
apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>m.
by rewrite measurement_pre_frame // meas0_assertionE.
Qed.
End CQPrimitiveFrame.


Module CQAuxiliaryDerivations.
(* Derived Sum and Linear rules; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion CQHoare CQAuxiliary.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem derives_sum total c (p q : pred cmem) (P Q R S : assertion) :
  (forall i, q i -> ~~ p i) ->
  (forall i, (S i : 'End(Hq)) = (mask p P i : 'End(Hq)) + (mask q Q i : 'End(Hq))) ->
  derives total (mask p P) c R -> derives total (mask q Q) c R ->
  derives total S c R.
Proof.
move=>Hdis HE /derives_sound HP /derives_sound HQ; apply: derives_complete.
exact: valid_disjoint_sum Hdis HE HP HQ.
Qed.

Theorem derives_linear_total (J : finType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, derives true (F j) c (G j)) -> derives true P c Q.
Proof.
move=>Hw HP HQ HD; apply: derives_complete.
apply: (@valid_finite_linear_total J w F G P Q c Hw HP HQ)=>j.
exact: derives_sound (HD j).
Qed.

Theorem derives_linear_partial (J : finType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) -> (\sum_j w j <= 1) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, derives false (F j) c (G j)) -> derives false P c Q.
Proof.
move=>Hw Hsum HP HQ HD; apply: derives_complete.
apply: (@valid_finite_linear_partial J w F G P Q c Hw Hsum HP HQ)=>j.
exact: derives_sound (HD j).
Qed.

Theorem derives_series_total (J : choiceType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, derives true (F j) c (G j)) -> derives true P c Q.
Proof.
move=>Hw HS HT HP HQ HD; apply: derives_complete.
apply: (@valid_series_total J w F G P Q c Hw HS HT HP HQ)=>j.
exact: derives_sound (HD j).
Qed.

Theorem derives_series_partial (J : choiceType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) -> summable w -> sum w <= 1 ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, derives false (F j) c (G j)) -> derives false P c Q.
Proof.
move=>Hw Hsw Hsum HS HT HP HQ HD; apply: derives_complete.
apply: (@valid_series_partial J w F G P Q c Hw Hsw Hsum HS HT HP HQ)=>j.
exact: derives_sound (HD j).
Qed.
End CQAuxiliaryDerivations.


Module CQQuantumCrossSpace.
(* Rectangular assertion-space SupOper; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame CQQuantumSpaceRules.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition rectangular_depolarizer (U V : chsType) : 'SO(U,V) :=
  ((dim U)%:R)^-1 *:
    krausso (fun ij : 'I_(dim U) * 'I_(dim V) => [>eb ij.2 : V; eb ij.1 : U<]).

Lemma rectangular_depolarizerE (U V : chsType) (A : 'End(U)) :
  rectangular_depolarizer U V A = ((dim U)%:R)^-1 *: (\Tr A *: (\1 : 'End(V))).
Proof.
rewrite /rectangular_depolarizer scale_soE kraussoE pair_bigV /=.
f_equal.
rewrite (onb_trlf eb A) scaler_suml; apply:eq_bigr=>i _.
under eq_bigr do rewrite adj_outp -comp_lfunA outp_compr outp_comp.
by rewrite -scaler_sumr sumonb_out.
Qed.

Lemma rectangular_depolarizer_cp (U V : chsType) :
  rectangular_depolarizer U V \is cpmap.
Proof.
rewrite -geso0_cpE /rectangular_depolarizer; apply: scalev_ge0.
- by rewrite invr_ge0 ler0n.
- by rewrite geso0_cpE is_cpmap.
Qed.

Lemma rectangular_depolarizer1 (U V : chsType) :
  rectangular_depolarizer U V \1 = \1.
Proof.
rewrite rectangular_depolarizerE /lftrace h2mx1 mxtrace1 scalerA mulVf ?scale1r //.
by rewrite gt_eqF // dim_proper_gt0.
Qed.

Lemma rectangular_depolarizer_dqo (U V : chsType) :
  (rectangular_depolarizer U V)^*o \is cptn.
Proof.
rewrite (CPMap_BuildE (rectangular_depolarizer_cp U V)) cp_isdqoE.
by rewrite rectangular_depolarizer1.
Qed.

Definition rectangular_depolarizing (U V : chsType) : 'DQO(U,V) :=
  DualQO_Build (rectangular_depolarizer_dqo U V).

Definition square_extension S T (F : 'DQO[msys]_(S,T)) : 'DQO[msys]_(S :|: T) :=
  castso (setUD_sub (finset.subsetUl S T), setUD_sub (finset.subsetUr S T))
    (tenso_dqoType (disjointXD S (S :|: T)) (disjointXD T (S :|: T)) F
      (rectangular_depolarizing 'H[msys]_((S :|: T) :\: S)
        'H[msys]_((S :|: T) :\: T))).

Lemma square_extension_lift S T (F : 'DQO[msys]_(S,T)) (A : 'F[msys]_S) :
  square_extension F (lift_lf (finset.subsetUl S T) A) =
    lift_lf (finset.subsetUr S T) (F A).
Proof.
rewrite /square_extension /lift_lf castsoE /= castlf_comp castlf_id.
rewrite -(@tenso_correct _ msys S T ((S :|: T) :\: S) ((S :|: T) :\: T)
  F (rectangular_depolarizer 'H[msys]_((S :|: T) :\: S)
    'H[msys]_((S :|: T) :\: T)) (disjointXD S (S :|: T))).
by rewrite rectangular_depolarizer1.
Qed.

Lemma square_extension_cylinder S T (F : 'DQO[msys]_(S,T)) (A : 'F[msys]_S) :
  liftfso (square_extension F) (liftf_lf A) = liftf_lf (F A).
Proof.
rewrite -{1}(liftf_lf2 (finset.subsetUl S T) A) liftfsoEf.
by rewrite square_extension_lift liftf_lf2.
Qed.

Lemma cylinder_tensor_action S T U R (E : 'SO[msys]_U)
    (F : 'SO[msys]_(S,T)) (A : 'F[msys]_(S :|: R)) :
  [disjoint S & R] -> [disjoint T & R] -> [disjoint R & U] ->
  (forall X : 'F[msys]_S, liftfso E (liftf_lf X) = liftf_lf (F X)) ->
  liftfso E (liftf_lf A) = liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) A).
Proof.
move=>HS HT Hd HC.
rewrite (onb_lfun2id deltav A) !linear_sum /=.
apply:eq_bigr=>i _; rewrite !linear_sum /=.
apply:eq_bigr=>j _; rewrite !linearZ /=; f_equal.
rewrite -tensodf id_soE.
rewrite [deltav j]dv_split [deltav i]dv_split -tenf_outp
  -(liftf_lf_compT _ _ HS) (liftfsoEf_compr _ _ _ Hd).
by rewrite HC (liftf_lf_compT _ _ HT).
Qed.

Lemma square_extension_tensor S T R (F : 'DQO[msys]_(S,T))
    (A : 'F[msys]_(S :|: R)) :
  [disjoint S & R] -> [disjoint T & R] ->
  liftfso (square_extension F) (liftf_lf A) =
    liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) A).
Proof.
move=>HS HT.
have Hd : [disjoint R & S :|: T].
  by rewrite disjoint_sym finset.disjoints_subset finset.subUset
    -!finset.disjoints_subset HS HT.
exact: cylinder_tensor_action HS HT Hd (square_extension_cylinder F).
Qed.

Definition cross_assertion (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (P : cmem -> 'FO[msys]_(S :|: R)) : assertion :=
  fun m => liftf_lf (ObsLf_Build
    (dqo_obslf (tenso_dqoType HS HT F (\:1 : 'DQO[msys]_R)) (P m))).

Lemma cross_assertionE (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (P : cmem -> 'FO[msys]_(S :|: R)) m :
  (@cross_assertion S T R F HS HT P m : 'End(Hq)) =
    liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) (P m)).
Proof. by []. Qed.

Lemma image_square_extension (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (P : cmem -> 'FO[msys]_(S :|: R)) :
  image (square_extension F) (lifted P) = @cross_assertion S T R F HS HT P.
Proof.
apply/funext=>m; apply/val_inj.
change (liftfso (square_extension F) (liftf_lf (P m)) =
  liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) (P m))).
exact: square_extension_tensor HS HT.
Qed.

Theorem derives_supoper_cross total c (S T R R' : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (HS' : [disjoint S & R']) (HT' : [disjoint T & R'])
    (P : cmem -> 'FO[msys]_(S :|: R))
    (Q : cmem -> 'FO[msys]_(S :|: R')) :
  [disjoint quantum_variables c & S :|: T] ->
  derives total (lifted P) c (lifted Q) ->
  derives total (@cross_assertion S T R F HS HT P) c
    (@cross_assertion S T R' F HS' HT' Q).
Proof.
move=>Hc HD; rewrite -!image_square_extension.
exact: derives_supoper Hc HD.
Qed.
End CQQuantumCrossSpace.


Module CQMemoryExtension.
(* Independence from unused finite quantum memory.
   See PROOF_NOTES.md for the depolarizer and partial-trace argument. *)


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
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame CQQuantumTrace.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma uniform_nonzero (U : chsType) : uniform_weight U != 0.
Proof. by rewrite /uniform_weight invr_eq0 pnatr_eq0 -lt0n dim_proper. Qed.

Lemma depolarizer_full (T : {set mlab}) (A : 'End(Hq)) :
  liftfso (depolarizer msys T) A =
  uniform_weight 'H[msys]_T *: liftf_lf (ptraceso T A).
Proof.
have E := @lift_depolarizer _ msys finset.setT T A.
by rewrite finset.setTI liftf_lf_id in E.
Qed.

Theorem denote_partial_trace c (T : {set mlab}) m out (rho : 'End(Hq)) :
  [disjoint quantum_variables c & T] ->
  liftf_lf (ptraceso T (denote c m out rho)) =
    denote c m out (liftf_lf (ptraceso T rho)).
Proof.
move=>Hdis.
have E := congr1 (fun F : 'SO(Hq) => F rho)
  (@denote_disjoint_commute c T (depolarizer msys T) Hdis m out).
rewrite !comp_soE !depolarizer_full linearZ /= in E.
apply: (@scalerI _ _ (uniform_weight 'H[msys]_T) (uniform_nonzero _)).
exact: esym E.
Qed.

Theorem denote_marginal_ext c (T : {set mlab}) m out (rho sigma : 'End(Hq)) :
  [disjoint quantum_variables c & T] -> ptraceso T rho = ptraceso T sigma ->
  ptraceso T (denote c m out rho) = ptraceso T (denote c m out sigma).
Proof.
move=>Hdis E; apply: liftf_lf_inj.
by rewrite !denote_partial_trace // E.
Qed.

Theorem apply_marginal_ext c (T : {set mlab})
  (d e : @CQState.state cmem Hq) :
  [disjoint quantum_variables c & T] ->
  (forall m, ptraceso T (d m) = ptraceso T (e m)) -> forall out,
  ptraceso T (CQKernel.apply (denote c) d out) =
    ptraceso T (CQKernel.apply (denote c) e out).
Proof.
move=>Hdis E out; rewrite !CQKernel.applyE.
rewrite (cvg_linearP_sum (x := fun m => denote c m out (d m))
  (f := ptraceso T) (superop_is_linear (ptraceso T))).
- by apply: norm_bounded_cvg; exact: CQKernel.columns_summable.
rewrite (cvg_linearP_sum (x := fun m => denote c m out (e m))
  (f := ptraceso T) (superop_is_linear (ptraceso T))).
- by apply: norm_bounded_cvg; exact: CQKernel.columns_summable.
apply:eq_sum=>m; exact: denote_marginal_ext Hdis (E m).
Qed.

Theorem partial_trace_product (T : {set mlab})
  (A : 'F[msys]_(finset.setT :\: T)) (B : 'F[msys]_T) :
  ptraceso T (liftf_lf A \o liftf_lf B) = \Tr B *: A.
Proof.
have Hd : [disjoint finset.setT :\: T & T].
  by rewrite finset.setTD disjointCX.
apply: liftf_lf_inj.
apply: (@scalerI _ _ (uniform_weight 'H[msys]_T) (uniform_nonzero _)).
rewrite -depolarizer_full liftfsoEf_compl // liftfsoEf depolarizerE
  !linearZ /= liftf_lf1 comp_lfun1r.
by rewrite !scalerA mulrC.
Qed.

Theorem normalized_memory_extension c (T : {set mlab}) m out
  (A : 'F[msys]_(finset.setT :\: T)) (B D : 'FD1('H[msys]_T)) :
  [disjoint quantum_variables c & T] ->
  ptraceso T (denote c m out (liftf_lf A \o liftf_lf B)) =
    ptraceso T (denote c m out (liftf_lf A \o liftf_lf D)).
Proof.
move=>Hdis; apply: denote_marginal_ext Hdis _.
by rewrite !partial_trace_product !den1f_trlf.
Qed.
End CQMemoryExtension.


Module CQPredicateAlgebra.
(* Lemma 4.16(3--5); see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame CQQuantumSpaceRules CQQuantumCrossSpace.
Local Notation Hq := 'H[msys]_finset.setT.

Section FiniteAlgebra.
Context {I J : choiceType} {H : chsType}.
Variable K : semType I J H H.

Theorem wp_finite_linear (T : finType) (w : T -> C)
    (F : T -> J -> 'FO(H)) (Q : J -> 'FO(H)) :
  (forall j, (Q j : 'End(H)) = \sum_t w t *: (F t j : 'End(H))) ->
  forall i, (wp K Q i : 'End(H)) = \sum_t w t *: (wp K (F t) i : 'End(H)).
Proof.
move=>HQ i; rewrite wpE.
pose terms t := w t *: Summable.build (term_summable K (F t) i).
have E : (fun j => (K i j)^*o (Q j)) =
    (\sum_t terms t : {summable J -> 'End(H)}).
  apply/funext=>j; rewrite summable_sumE HQ linear_sum /=.
  apply:eq_bigr=>t _; by rewrite /terms /= /term linearZ.
rewrite E summable_sum_sum; apply:eq_bigr=>t _.
by rewrite /terms summable_sumZ wpE.
Qed.

Theorem wlp_finite_affine (T : finType) (w : T -> C)
    (F : T -> J -> 'FO(H)) (Q : J -> 'FO(H)) :
  \sum_t w t = 1 ->
  (forall j, (Q j : 'End(H)) = \sum_t w t *: (F t j : 'End(H))) ->
  forall i, (wlp K Q i : 'End(H)) = \sum_t w t *: (wlp K (F t) i : 'End(H)).
Proof.
move=>Hw HQ i.
have HE j : (complement Q j : 'End(H)) =
    \sum_t w t *: (complement (F t) j : 'End(H)).
  change (\1 - (Q j : 'End(H)) = \sum_t w t *: (\1 - (F t j : 'End(H)))).
  under eq_bigr do rewrite scalerBr.
  by rewrite sumrB -scaler_suml Hw scale1r HQ.
change (\1 - (wp K (complement Q) i : 'End(H)) =
  \sum_t w t *: (\1 - (wp K (complement (F t)) i : 'End(H)))).
rewrite (@wp_finite_linear T w (fun t => complement (F t)) (complement Q) HE).
under [RHS]eq_bigr do rewrite scalerBr.
by rewrite sumrB -scaler_suml Hw scale1r.
Qed.

End FiniteAlgebra.

Theorem wlp_image_unital c S (F : 'DQO[msys]_S) Q :
  [disjoint quantum_variables c & S] -> F \1 = \1 -> forall s,
  (wlp (denote c) (image F Q) s : 'End(Hq)) = liftfso F (wlp (denote c) Q s).
Proof.
move=>Hdis HF s; rewrite !wlp_decompose (wp_image F Q Hdis) linearD.
change ((\1 - (wp (denote c) semantic_top s : 'End(Hq))) +
  liftfso F (wp (denote c) Q s) =
  liftfso F (\1 - (wp (denote c) semantic_top s : 'End(Hq))) +
  liftfso F (wp (denote c) Q s)).
by rewrite (@loss_unital c S F s Hdis HF).
Qed.

Lemma square_extension_unital S T (F : 'DQO[msys]_(S,T)) :
  F \1 = \1 -> square_extension F \1 = \1.
Proof.
move=>HF; have E := square_extension_lift F (\1 : 'F[msys]_S).
by rewrite HF !lift_lf1 in E.
Qed.

Theorem wp_cross c (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (Q : cmem -> 'FO[msys]_(S :|: R)) :
  [disjoint quantum_variables c & S :|: T] -> forall s,
  (wp (denote c) (@cross_assertion S T R F HS HT Q) s : 'End(Hq)) =
    liftfso (square_extension F) (wp (denote c) (lifted Q) s).
Proof.
move=>Hdis s; rewrite -image_square_extension.
exact: (@wp_image c (S :|: T) (square_extension F) (lifted Q) Hdis s).
Qed.

Theorem wlp_cross_le c (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (Q : cmem -> 'FO[msys]_(S :|: R)) :
  [disjoint quantum_variables c & S :|: T] -> forall s,
  liftfso (square_extension F) (wlp (denote c) (lifted Q) s) ⊑
    (wlp (denote c) (@cross_assertion S T R F HS HT Q) s : 'End(Hq)).
Proof.
move=>Hdis s; rewrite -image_square_extension.
exact: (@pre_image_le false c _ (square_extension F) (lifted Q) s Hdis).
Qed.

Theorem wlp_cross_unital c (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (Q : cmem -> 'FO[msys]_(S :|: R)) :
  [disjoint quantum_variables c & S :|: T] -> F \1 = \1 -> forall s,
  (wlp (denote c) (@cross_assertion S T R F HS HT Q) s : 'End(Hq)) =
    liftfso (square_extension F) (wlp (denote c) (lifted Q) s).
Proof.
move=>Hdis HF s; rewrite -image_square_extension.
exact: (@wlp_image_unital c (S :|: T) (square_extension F)
  (lifted Q) Hdis (@square_extension_unital S T F HF) s).
Qed.
End CQPredicateAlgebra.


Module CQPredicateSupport.
(* Lemma 4.14(1); see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage CQQuantumFrame CQQuantumSpaceRules CQQuantumTrace CQMemoryExtension CQPredicateAlgebra.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma complement_difference (S : {set mlab}) : finset.setT :\: ~: S = S.
Proof. by rewrite finset.setTD finset.setCK. Qed.

Definition local_operator (S : {set mlab}) (A : 'End(Hq)) : 'F[msys]_S :=
  castlf (complement_difference S, complement_difference S)
    (uniform_weight 'H[msys]_(~: S) *: ptraceso (~: S) A).

Lemma local_operator_cylinder S A :
  liftf_lf (local_operator S A) = liftfso (depolarizer msys (~: S)) A.
Proof.
by rewrite /local_operator liftf_lf_cast linearZ /= -depolarizer_full.
Qed.

Lemma local_operator_effect S (A : 'FO(Hq)) : local_operator S A \is obslf.
Proof.
rewrite liftf_lf_obsE local_operator_cylinder.
exact: (dqo_obslf (liftfso (depolarizing msys (~: S))) A).
Qed.

Definition local_assertion (S : {set mlab}) (P : assertion) : cmem -> 'FO[msys]_S :=
  fun m => ObsLf_Build (local_operator_effect S (P m)).

Lemma local_assertionE S P m :
  (local_assertion S P m : 'F[msys]_S) = local_operator S (P m).
Proof. by []. Qed.

Lemma depolarizer_unital (T : {set mlab}) : depolarizer msys T \1 = \1.
Proof.
rewrite depolarizerE /uniform_weight /lftrace h2mx1 mxtrace1 scalerA mulVf.
- by rewrite gt_eqF // dim_proper_gt0.
- by rewrite scale1r.
Qed.

Lemma depolarizer_fixes_local S (P : cmem -> 'FO[msys]_S) :
  image (depolarizing msys (~: S)) (lifted P) = lifted P.
Proof.
apply/funext=>m; apply/val_inj.
change (liftfso (depolarizer msys (~: S)) (liftf_lf (P m)) = liftf_lf (P m)).
have Hd : [disjoint S & ~: S] := disjointXC S.
by rewrite (lift_tensor_image _ _ Hd) depolarizer_unital (liftf_lf_tenf1r _ Hd).
Qed.

Definition local_pre total c (S : {set mlab}) (Q : cmem -> 'FO[msys]_S) :=
  local_assertion S (pre total c (lifted Q)).

Theorem local_preE total c (S : {set mlab}) (Q : cmem -> 'FO[msys]_S) :
  quantum_variables c :<=: S -> forall m,
  (pre total c (lifted Q) m : 'End(Hq)) = liftf_lf (local_pre total c Q m).
Proof.
move=>Hsub m.
have Hdis : [disjoint quantum_variables c & ~: S].
  by rewrite -finset.subsets_disjoint.
rewrite /local_pre local_assertionE local_operator_cylinder.
case: total.
- have E := @wp_image c (~: S) (depolarizing msys (~: S)) (lifted Q) Hdis m.
  rewrite depolarizer_fixes_local in E; exact: E.
- have H1 : depolarizing msys (~: S) \1 = \1 := depolarizer_unital (~: S).
  have E := @wlp_image_unital c (~: S) (depolarizing msys (~: S))
    (lifted Q) Hdis H1 m.
  rewrite depolarizer_fixes_local in E; exact: E.
Qed.

Theorem pre_quantum_support total c (S : {set mlab}) (Q : cmem -> 'FO[msys]_S) :
  quantum_variables c :<=: S ->
  pre total c (lifted Q) = lifted (local_pre total c Q).
Proof.
move=>Hsub; apply/funext=>m; apply/val_inj.
exact: (@local_preE total c S Q Hsub m).
Qed.
End CQPredicateSupport.
