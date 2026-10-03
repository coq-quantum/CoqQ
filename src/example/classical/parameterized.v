(* Finite parameter and register selection, classical paper pp. 16, 23, 31.
   The Param rule uses the correct wp formula; see C4 in PROOF_GAPS.md. *)
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
From quantum.example.classical Require Import state assertion kernel kernel_expectation language predicate.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


From quantum.example.classical Require Import hoare rules primitive.

Module CQParameterized.
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
  if eval choose m is Some i then CQRules.pre true (branch i) Q m else 0%:VF.

Lemma selector_list_selected indices i m Q : i \in indices -> eval choose m = Some i ->
  CQRules.pre true (selector_list indices) Q m = CQRules.pre true (branch i) Q m.
Proof.
elim: indices=>[|j rest IH]; first by rewrite in_nil.
rewrite inE=>/orP[/eqP->|Hi] He.
- change (CQRules.pre true (Conditional (selector_guard j) (branch j) (selector_list rest)) Q m =
    CQRules.pre true (branch j) Q m).
  by rewrite CQRules.pre_conditional /conditional /selector_guard /eval /= -/(eval choose m) He eqxx.
- change (CQRules.pre true (Conditional (selector_guard j) (branch j) (selector_list rest)) Q m =
    CQRules.pre true (branch i) Q m).
  rewrite CQRules.pre_conditional /conditional /selector_guard /eval /= -/(eval choose m) He /=.
  case: eqP=>[Eij|Hne].
  + by case: Eij=>->.
  + exact: IH Hi He.
Qed.

Lemma selector_list_none indices m Q : eval choose m = None ->
  CQRules.pre true (selector_list indices) Q m = 0%:VF.
Proof.
move=>He; elim: indices=>[|i rest IH].
- by rewrite /selector_list /CQRules.pre /xp /= wp_abort.
- change (CQRules.pre true (Conditional (selector_guard i) (branch i) (selector_list rest)) Q m = 0%:VF).
  by rewrite CQRules.pre_conditional /conditional /selector_guard /eval /= -/(eval choose m) He.
Qed.

Lemma selector_preE Q : CQRules.pre true selector_command Q = selector_pre Q.
Proof.
apply/funext=>m; rewrite /selector_pre.
case He: (eval choose m)=>[i|].
- apply: selector_list_selected He; exact: mem_enum.
- exact: selector_list_none He.
Qed.

Lemma selector_pre_sum Q m : (selector_pre Q m : 'End(Hq)) =
  \sum_(i : I) (if eval choose m == Some i then (CQRules.pre true (branch i) Q m : 'End(Hq)) else 0).
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
Proof. apply: CQHoare.valid_from_total; rewrite -selector_preE; exact: CQRules.pre_valid. Qed.

Theorem derives_selector total Q : CQRules.derives total (selector_pre Q) selector_command Q.
Proof. apply: CQRules.derives_complete; exact: valid_selector. Qed.
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
  (CQRules.pre true (parameterized_unitary q U e) Q m : 'End(Hq)) =
  \sum_(i : 'I_K) (if eval e m == Posz (val i).+1 then
    (liftfso (formso (tf2f q q (U i))))^*o (Q m) else 0).
Proof.
rewrite selector_preE selector_pre_sum; apply: eq_bigr=>i _.
rewrite parameter_selector_eq; case: ifP=>// _.
exact: CQPrimitive.unitary_pre.
Qed.

Theorem derives_parameterized total t K (q : wf_qreg t) (U : 'I_K -> 'FU('Ht t)) e Q :
  CQRules.derives total (parameterized_pre q U e Q) (parameterized_unitary q U e) Q.
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
  (CQRules.pre true (selected_unitary q U es e) Q m : 'End(Hq)) =
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
  CQRules.derives total (selected_pre q U es e Q) (selected_unitary q U es e) Q.
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
