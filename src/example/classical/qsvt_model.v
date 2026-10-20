(* Exact QSVT: projected-unitary gates and operator identities. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From quantum Require Import compat.
From quantum.external Require Import complex spectral.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import exp trigo.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology svd
  mxnorm hermitian inhabited prodvect tensor quantum hspace.
From mathcomp Require Import ring_tactic.
From quantum.example.classical Require Import qsvt_poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module QSVTModel.
Import trigo.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Lemma expi_conj (theta : R) : (expi theta)^* = expi (- theta).
Proof. by rewrite /expi; simpc; rewrite cosN sinN. Qed.

Lemma expi_unit (theta : R) : expi (- theta) * expi theta = 1.
Proof. by rewrite -expiD addNr expi0. Qed.

Section Phases.
Variable (H : chsType) (P : 'FP(H)).

Definition projector_phase_raw (theta : R) : 'End(H) :=
  expi theta *: (P : 'End(H)) +
  expi (- theta) *: (\1 - (P : 'End(H))).

Lemma projector_complement_left : (P \o (\1 - (P : 'End(H))) = 0)%VF.
Proof. by rewrite linearBr /= comp_lfun1r projf_idem subrr. Qed.

Lemma projector_complement_right : ((\1 - (P : 'End(H))) \o P = 0)%VF.
Proof. by rewrite linearBl /= comp_lfun1l projf_idem subrr. Qed.

Lemma projector_complement_idem :
  ((\1 - (P : 'End(H))) \o (\1 - (P : 'End(H))) = \1 - (P : 'End(H)))%VF.
Proof.
by rewrite linearBl /= comp_lfun1l projector_complement_left subr0.
Qed.

Lemma projector_phase_adjoint theta :
  (projector_phase_raw theta)^A = projector_phase_raw (- theta).
Proof.
by rewrite /projector_phase_raw adjfD !adjfZ expi_conj expi_conj
  adjfB adjf1 !hermf_adjE opprK.
Qed.

Lemma projector_phase_unitary theta : projector_phase_raw theta \is unitarylf.
Proof.
apply/unitarylfP; rewrite projector_phase_adjoint /projector_phase_raw opprK.
rewrite linearDl /= !linearDr /= !linearZl /= !linearZr /=
  projf_idem projector_complement_left projector_complement_right
  projector_complement_idem !scaler0 !addr0 add0r !scalerA.
by rewrite expi_unit mulrC expi_unit !scale1r addrC subrK.
Qed.

Definition projector_phase theta : 'FU(H) :=
  UnitaryLf_Build (projector_phase_unitary theta).

Lemma projector_phaseE theta :
  (projector_phase theta : 'End(H)) = projector_phase_raw theta.
Proof. by []. Qed.

Lemma projector_phase_on (K : chsType) (M : 'Hom(K,H)) theta :
  P \o M = M -> projector_phase theta \o M = expi theta *: M.
Proof.
move=>PM; rewrite projector_phaseE /projector_phase_raw linearDl /=
  !linearZl /= linearBl /= comp_lfun1l PM subrr scaler0 addr0.
by [].
Qed.

Lemma projector_phase_off (K : chsType) (M : 'Hom(K,H)) theta :
  P \o M = 0 -> projector_phase theta \o M = expi (-theta) *: M.
Proof.
move=>PM; rewrite projector_phaseE /projector_phase_raw linearDl /=
  !linearZl /= linearBl /= comp_lfun1l PM subr0 scaler0 add0r.
by [].
Qed.
End Phases.

(* Evaluation uses MathComp's existing algebra morphism; multiplication in
   this endomorphism algebra is CoqQ's forward composition. *)
Definition peval (H : chsType) (B : 'End(H)) (p : {poly C}) : 'End(H) :=
  @horner_alg C (@chsf_comp_algType H) B p.

Section Evaluation.
Variables (H : chsType) (B : 'End(H)).
Lemma pevalC a : peval B a%:P = a *: (\1 : 'End(H)).
Proof. by rewrite /peval horner_algC. Qed.
Lemma pevalX : peval B 'X = B.
Proof. by rewrite /peval horner_algX. Qed.
Lemma pevalM p q : peval B (p*q) = peval B p \o peval B q.
Proof. by rewrite /peval rmorphM. Qed.
Lemma pevalD p q : peval B (p+q) = peval B p + peval B q.
Proof. by rewrite /peval rmorphD. Qed.
Lemma pevalB p q : peval B (p-q) = peval B p - peval B q.
Proof. by rewrite /peval rmorphB. Qed.
Lemma peval0 : peval B 0 = 0.
Proof. by rewrite /peval rmorph0. Qed.
Lemma peval1 : peval B 1 = \1.
Proof. by rewrite /peval rmorph1. Qed.
Lemma pevalZ k p : peval B (k*:p) = k*:peval B p.
Proof.
rewrite /peval -mul_polyC rmorphM /= horner_algC.
change ((k *: (\1 : 'End(H))) \o peval B p = k*:peval B p).
by rewrite -comp_lfunZl comp_lfun1l.
Qed.
End Evaluation.

Definition range_projector (H K : chsType) (J : 'FI(K,H)) : 'FP(H) :=
  [proj of formlf J (\1 : 'FP(K))].
Lemma range_projectorE (H K : chsType) (J : 'FI(K,H)) :
  (range_projector J : 'End(H)) = J \o J^A.
Proof. exact: formlf1E. Qed.
Lemma range_projector_on (H K : chsType) (J : 'FI(K,H)) :
  range_projector J \o J = J.
Proof. by rewrite range_projectorE isofK. Qed.
Lemma range_projector_off (H K L : chsType) (J : 'FI(K,H))
    (M : 'Hom(L,H)) :
  J^A \o M = 0 -> range_projector J \o M = 0.
Proof.
by move=>JM; rewrite range_projectorE -comp_lfunA JM comp_lfun0r.
Qed.

Section Encodings.
Variables (H HR HL : chsType) (U : 'FU(H)).
Variables (JR : 'FI(HR,H)) (JL : 'FI(HL,H)).

Definition encoded : 'Hom(HR,HL) := JL^A \o U \o JR.
Definition gram : 'End(HR) := encoded^A \o encoded.
Definition left_defect : 'Hom(HR,H) := (U \o JR) - (JL \o encoded).
Definition right_defect : 'Hom(HR,H) :=
  (U^A \o JL \o encoded) - (JR \o gram).

Lemma encoded_adjoint : encoded^A = JR^A \o U^A \o JL.
Proof. by rewrite /encoded !adjf_comp adjfK comp_lfunA. Qed.

Lemma gram_adjoint : gram^A = gram.
Proof. by rewrite /gram adjf_comp adjfK. Qed.

Lemma left_defect_orthogonal : JL^A \o left_defect = 0.
Proof.
by rewrite /left_defect linearBr /= !comp_lfunA isofE comp_lfun1l
  -/encoded subrr.
Qed.

Lemma right_defect_orthogonal : JR^A \o right_defect = 0.
Proof.
rewrite /right_defect linearBr /= !comp_lfunA isofE comp_lfun1l.
by rewrite -encoded_adjoint -/gram subrr.
Qed.

Lemma signal_right : U \o JR = (JL \o encoded) + left_defect.
Proof. by rewrite /left_defect addrC subrK. Qed.

Lemma signal_right_defect :
  U \o right_defect =
  (JL \o encoded \o (\1 - gram)) - (left_defect \o gram).
Proof.
rewrite /right_defect linearBr /= !comp_lfunA unitaryf_formV comp_lfun1l.
rewrite linearBr /= comp_lfun1r /left_defect linearBl /=.
by rewrite !comp_lfunA !linearBl /= opprB addrA subrK.
Qed.

Lemma signal_left : U^A \o JL \o encoded = (JR \o gram) + right_defect.
Proof. by rewrite /right_defect addrC subrK. Qed.

Lemma signal_left_defect :
  U^A \o left_defect = (JR \o (\1 - gram)) - right_defect.
Proof.
rewrite /left_defect linearBr /= !comp_lfunA unitaryf_form comp_lfun1l.
rewrite /right_defect linearBr /= comp_lfun1r opprB addrA.
by rewrite subrK /encoded !comp_lfunA.
Qed.
End Encodings.

Section DefectGrams.
Variables (H HR HL : chsType) (U : 'FU(H)).
Variables (JR : 'FI(HR,H)) (JL : 'FI(HL,H)).
Let A := encoded U JR JL.
Let B := gram U JR JL.
Let KL := left_defect U JR JL.

Lemma left_defect_gram : KL^A \o KL = \1 - B.
Proof.
rewrite /KL /left_defect adjfB (adjf_comp U JR)
  (adjf_comp JL (encoded U JR JL)) !linearBr !linearBl /=.
change ((((JR^A \o U^A) \o (U \o JR)) -
  ((A^A \o JL^A) \o (U \o JR))) -
  (((JR^A \o U^A) \o (JL \o A)) -
  ((A^A \o JL^A) \o (JL \o A))) = \1 - B).
rewrite !comp_lfunA !isofK isofE -encoded_adjoint -/A -/B.
by rewrite -!comp_lfunA (comp_lfunA JL^A U JR) -/A -/B subrr subr0.
Qed.
End DefectGrams.

Lemma compose_subr (K0 K1 K2 : chsType) (f : 'Hom(K1,K2))
    (g h : 'Hom(K0,K1)) : f \o (g-h) = (f \o g) - (f \o h).
Proof. exact: linearBr. Qed.
Lemma compose_subl (K0 K1 K2 : chsType) (f g : 'Hom(K1,K2))
    (h : 'Hom(K0,K1)) : (f-g) \o h = (f \o h) - (g \o h).
Proof. exact: linearBl. Qed.

(* The two parity cases of the polynomial recurrence use Y = X^2. *)
Definition split_step (b : bool) (theta : R)
    (ab : {poly C} * {poly C}) :=
  if b then
    ((expi theta)%:P*('X*ab.1+(1-'X)*ab.2),
     (expi (-theta))%:P*(ab.1-ab.2))
  else
    ((expi theta)%:P*(ab.1+(1-'X)*ab.2),
     (expi (-theta))%:P*(ab.1-'X*ab.2)).
Fixpoint split_pair d (phi : nat -> R) t : {poly C} * {poly C} :=
  if t is t'.+1 then
    split_step (odd t') (phi (d-t'.+1)%N) (split_pair d phi t')
  else ((expi (phi d))%:P,0).

Definition scalar_reconstruct b (ab : {poly C} * {poly C}) :=
  if b then ('X*(ab.1 \Po 'X^2), ab.2 \Po 'X^2)
  else (ab.1 \Po 'X^2, 'X*(ab.2 \Po 'X^2)).

Lemma scalar_reconstruct_step b theta ab :
  scalar_reconstruct (~~b) (split_step b theta ab) =
  QSVTPolynomial.qsp_step theta (scalar_reconstruct b ab).
Proof.
case: ab=>a c; case: b;
  rewrite /scalar_reconstruct /split_step /QSVTPolynomial.qsp_step
    /QSVTPolynomial.defect QSVTPolynomial.expi_conj /=.
all: rewrite !(comp_polyM, comp_polyB, comp_polyD, comp_polyC, comp_polyX).
all: congr (_, _); ring.
Qed.

Fixpoint scalar_pair d (phi : nat -> R) t : {poly C} * {poly C} :=
  if t is t'.+1 then QSVTPolynomial.qsp_step (phi (d-t'.+1)%N)
    (scalar_pair d phi t')
  else ((expi (phi d))%:P,0).

Lemma scalar_split d phi t :
  scalar_reconstruct (odd t) (split_pair d phi t) = scalar_pair d phi t.
Proof.
elim: t=>[|t IH].
- by rewrite /= /scalar_reconstruct /= comp_polyC comp_poly0 mulr0.
- change (scalar_reconstruct (~~odd t)
    (split_step (odd t) (phi (d-t.+1)%N) (split_pair d phi t)) =
    QSVTPolynomial.qsp_step (phi (d-t.+1)%N) (scalar_pair d phi t)).
  by rewrite scalar_reconstruct_step IH.
Qed.

Lemma split_first_even d phi t : odd t = false ->
  even_poly (scalar_pair d phi t).1 = (split_pair d phi t).1.
Proof.
move=>Et; have E := congr1 fst (scalar_split d phi t).
rewrite Et /scalar_reconstruct /= in E.
by rewrite -E QSVTPolynomial.even_poly_compX2.
Qed.

Lemma split_first_odd d phi t : odd t = true ->
  odd_poly (scalar_pair d phi t).1 = (split_pair d phi t).1.
Proof.
move=>Et; have E := congr1 fst (scalar_split d phi t).
rewrite Et /scalar_reconstruct /= in E.
by rewrite -E mulrC odd_polyMX QSVTPolynomial.even_poly_compX2.
Qed.

Fixpoint phase_prefix d (phi : nat -> R) t :=
  if t is t'.+1 then phi (d-t'.+1)%N :: phase_prefix d phi t'
  else [::].
Lemma scalar_pairE d phi t : scalar_pair d phi t =
  QSVTPolynomial.qsp_pair (phase_prefix d phi t) (phi d).
Proof. by elim: t=>[|t IH] //=; rewrite IH. Qed.
Lemma phase_prefix_size d phi t : size (phase_prefix d phi t) = t.
Proof. by elim: t=>[|t IH] //=; rewrite IH. Qed.
Lemma phase_prefix_iota d phi t : (t<=d)%N ->
  phase_prefix d phi t = map phi (iota (d-t)%N t).
Proof.
elim: t=>[|t IH] Ht; first by [].
rewrite /= (IH (leq_trans (leqnSn _) Ht)).
by rewrite subnSK.
Qed.
Lemma phase_prefix_complete d phi :
  phase_prefix d phi d = map phi (iota 0 d).
Proof. by rewrite phase_prefix_iota // subnn. Qed.
Lemma scalar_pair_from_list (prefix : seq R) last :
  scalar_pair (size prefix) (nth 0 (rcons prefix last)) (size prefix) =
  QSVTPolynomial.qsp_pair prefix last.
Proof.
rewrite scalar_pairE phase_prefix_complete nth_rcons ltnn eqxx.
by rewrite map_nth_iota0 ?size_rcons ?leqnSn //
  -cats1 take_cat ltnn subnn take0 cats0.
Qed.
Lemma scalar_pair_valid d phi t :
  QSVTPolynomial.valid_pair t
    (scalar_pair d phi t).1 (scalar_pair d phi t).2.
Proof.
have h := QSVTPolynomial.qsp_pair_valid (phase_prefix d phi t) (phi d).
by rewrite phase_prefix_size -scalar_pairE in h.
Qed.

Definition poly_real (p : {poly C}) :=
  (2:C)^-1 *: (p+QSVTPolynomial.poly_star p).
Lemma even_poly_star (p : {poly C}) :
  even_poly (QSVTPolynomial.poly_star p) =
  QSVTPolynomial.poly_star (even_poly p).
Proof.
by apply/polyP=>i; rewrite !(coef_even_poly,QSVTPolynomial.poly_star_coef).
Qed.
Lemma odd_poly_star (p : {poly C}) :
  odd_poly (QSVTPolynomial.poly_star p) =
  QSVTPolynomial.poly_star (odd_poly p).
Proof.
by apply/polyP=>i; rewrite !(coef_odd_poly,QSVTPolynomial.poly_star_coef).
Qed.
Lemma even_poly_real (p : {poly C}) :
  even_poly (poly_real p) = poly_real (even_poly p).
Proof. by rewrite /poly_real linearZ /= even_polyD even_poly_star. Qed.
Lemma odd_poly_real (p : {poly C}) :
  odd_poly (poly_real p) = poly_real (odd_poly p).
Proof. by rewrite /poly_real linearZ /= odd_polyD odd_poly_star. Qed.
Lemma poly_real0 : poly_real 0 = 0.
Proof.
by rewrite /poly_real QSVTPolynomial.poly_star0 addr0 scaler0.
Qed.

Lemma split_second d phi t :
  (if odd t then even_poly (scalar_pair d phi t).2
   else odd_poly (scalar_pair d phi t).2) = (split_pair d phi t).2.
Proof.
have E := congr1 snd (scalar_split d phi t).
case Et: (odd t); rewrite Et /scalar_reconstruct /= in E.
- by rewrite -E QSVTPolynomial.even_poly_compX2.
- by rewrite -E mulrC odd_polyMX QSVTPolynomial.even_poly_compX2.
Qed.

Lemma scalar_pair_neg d phi t : scalar_pair d (fun j=>-phi j) t =
  (QSVTPolynomial.poly_star (scalar_pair d phi t).1,
   QSVTPolynomial.poly_star (scalar_pair d phi t).2).
Proof.
elim: t=>[|t IH].
- change (((expi (-phi d))%:P,0) =
    (QSVTPolynomial.poly_star (expi (phi d))%:P,
     QSVTPolynomial.poly_star (0:{poly C}))).
  by rewrite QSVTPolynomial.poly_starC QSVTPolynomial.poly_star0
    -QSVTPolynomial.expi_conj.
- change (QSVTPolynomial.qsp_step (-phi (d-t.+1)%N)
    (scalar_pair d (fun j=>-phi j) t) =
    (QSVTPolynomial.poly_star (QSVTPolynomial.qsp_step
      (phi (d-t.+1)%N) (scalar_pair d phi t)).1,
     QSVTPolynomial.poly_star (QSVTPolynomial.qsp_step
      (phi (d-t.+1)%N) (scalar_pair d phi t)).2)).
  rewrite IH; case: (scalar_pair d phi t)=>p q;
    exact: QSVTPolynomial.qsp_step_neg.
Qed.

Lemma split_pair_neg d phi t : split_pair d (fun j=>-phi j) t =
  (QSVTPolynomial.poly_star (split_pair d phi t).1,
   QSVTPolynomial.poly_star (split_pair d phi t).2).
Proof.
apply: injective_projections; simpl.
- case Et: (odd t).
  + by rewrite -(split_first_odd d (fun j=>-phi j) Et) scalar_pair_neg /=
      odd_poly_star (split_first_odd d phi Et).
  + by rewrite -(split_first_even d (fun j=>-phi j) Et) scalar_pair_neg /=
      even_poly_star (split_first_even d phi Et).
- rewrite -(split_second d (fun j=>-phi j) t) scalar_pair_neg /=.
  by case Et: (odd t); rewrite ?even_poly_star ?odd_poly_star
    -(split_second d phi t) Et.
Qed.

(* Independent polynomial singular-value transformation.  The full square
   right Gram operator retains p(0) on every right kernel direction. *)
Definition sv_even (H K : chsType) (p : {poly C}) (A : 'Hom(H,K)) :=
  peval (A^A \o A) (even_poly p).
Definition sv_odd (H K : chsType) (p : {poly C}) (A : 'Hom(H,K)) :=
  A \o peval (A^A \o A) (odd_poly p).

Section Lifting.
Variables (H HR HL : chsType) (U : 'FU(H)).
Variables (JR : 'FI(HR,H)) (JL : 'FI(HL,H)).
Let A := encoded U JR JL.
Let B := gram U JR JL.
Let KL := left_defect U JR JL.
Let KR := right_defect U JR JL.
Let PR := range_projector JR.
Let PL := range_projector JL.

Definition even_column (a b : {poly C}) : 'Hom(HR,H) :=
  (JR \o peval B a) + (KR \o peval B b).
Definition odd_column (a b : {poly C}) : 'Hom(HR,H) :=
  (JL \o A \o peval B a) + (KL \o peval B b).

Lemma even_signal a b : U \o even_column a b =
  (JL \o A \o (peval B a + ((\1 - B) \o peval B b))) +
  (KL \o (peval B a - (B \o peval B b))).
Proof.
rewrite /even_column comp_lfunDr
  (comp_lfunA U JR (peval B a)) (comp_lfunA U KR (peval B b))
  (signal_right U JR JL) (signal_right_defect U JR JL).
rewrite (compose_subl (JL \o A \o (\1 - B)) (KL \o B) (peval B b))
  (compose_subr KL (peval B a) (B \o peval B b)).
rewrite (comp_lfunDl (JL \o A) KL (peval B a))
  (comp_lfunDr (JL \o A) (peval B a) ((\1 - B) \o peval B b)).
rewrite (comp_lfunA (JL \o A) (\1 - B) (peval B b))
  (comp_lfunA KL B (peval B b)).
by rewrite addrACA.
Qed.

Lemma odd_signal a b : U^A \o odd_column a b =
  (JR \o ((B \o peval B a) + ((\1 - B) \o peval B b))) +
  (KR \o (peval B a - peval B b)).
Proof.
rewrite /odd_column comp_lfunDr
  (comp_lfunA U^A (JL \o A) (peval B a)) (comp_lfunA U^A JL A)
  (comp_lfunA U^A KL (peval B b))
  (signal_left U JR JL) (signal_left_defect U JR JL).
rewrite (compose_subl (JR \o (\1 - B)) KR (peval B b))
  (compose_subr KR (peval B a) (peval B b))
  (comp_lfunDl (JR \o B) KR (peval B a))
  (comp_lfunDr JR (B \o peval B a) ((\1 - B) \o peval B b))
  (comp_lfunA JR B (peval B a)) (comp_lfunA JR (\1 - B) (peval B b)).
by rewrite addrACA.
Qed.

Lemma left_phase_column theta a b :
  projector_phase PL theta \o odd_column a b =
  (expi theta *: (JL \o A \o peval B a)) +
  (expi (-theta) *: (KL \o peval B b)).
Proof.
rewrite /odd_column comp_lfunDr
  (comp_lfunA _ (JL \o A) (peval B a)) (comp_lfunA _ JL A)
  (projector_phase_on _ (range_projector_on JL)).
rewrite (comp_lfunA _ KL (peval B b))
  (projector_phase_off _ (range_projector_off
    (left_defect_orthogonal U JR JL))).
by rewrite -!comp_lfunZl.
Qed.

Lemma right_phase_column theta a b :
  projector_phase PR theta \o even_column a b =
  (expi theta *: (JR \o peval B a)) +
  (expi (-theta) *: (KR \o peval B b)).
Proof.
rewrite /even_column comp_lfunDr (comp_lfunA _ JR (peval B a))
  (projector_phase_on _ (range_projector_on JR))
  (comp_lfunA _ KR (peval B b))
  (projector_phase_off _ (range_projector_off
    (right_defect_orthogonal U JR JL))).
by rewrite -!comp_lfunZl.
Qed.

Lemma signal_even_poly a b : U \o even_column a b =
  odd_column (a + (1-'X)*b) (a-'X*b).
Proof.
rewrite /odd_column (pevalB B a ('X*b)) (pevalD B a ((1-'X)*b))
  !pevalM (pevalB B 1 'X) peval1 pevalX.
exact: even_signal.
Qed.

Lemma signal_odd_poly a b : U^A \o odd_column a b =
  even_column ('X*a+(1-'X)*b) (a-b).
Proof.
rewrite /even_column (pevalB B a b) (pevalD B ('X*a) ((1-'X)*b))
  !pevalM (pevalB B 1 'X) peval1 pevalX.
exact: odd_signal.
Qed.

Lemma phase_even_poly theta a b :
  projector_phase PR theta \o even_column a b =
  even_column ((expi theta)%:P*a) ((expi (-theta))%:P*b).
Proof.
rewrite right_phase_column /even_column !pevalM !pevalC.
by rewrite -!comp_lfunZl !comp_lfun1l -!comp_lfunZr.
Qed.

Lemma phase_odd_poly theta a b :
  projector_phase PL theta \o odd_column a b =
  odd_column ((expi theta)%:P*a) ((expi (-theta))%:P*b).
Proof.
rewrite left_phase_column /odd_column !pevalM !pevalC.
by rewrite -!comp_lfunZl !comp_lfun1l -!comp_lfunZr.
Qed.

Fixpoint qsvt_prefix d (phi : nat -> R) t : 'FU(H) :=
  if t is t'.+1 then
    [unitary of projector_phase (if odd t'.+1 then PL else PR)
      (phi (d-t'.+1)%N) \o
      (if odd t' then [unitary of U^A] else U) \o qsvt_prefix d phi t']
  else projector_phase PR (phi d).

Theorem qsvt_full_column d phi t : qsvt_prefix d phi t \o JR =
  if odd t then odd_column (split_pair d phi t).1 (split_pair d phi t).2
  else even_column (split_pair d phi t).1 (split_pair d phi t).2.
Proof.
elim: t=>[|t IH].
- rewrite /= (projector_phase_on _ (range_projector_on JR))
    /even_column pevalC peval0 comp_lfun0r addr0.
  by rewrite -comp_lfunZr comp_lfun1r.
- rewrite /= -comp_lfunA -comp_lfunA IH.
  case Et: (odd t).
  + by rewrite /= signal_odd_poly phase_even_poly.
  + by rewrite /= signal_even_poly phase_odd_poly.
Qed.

Corollary qsvt_even_block d phi t : odd t = false ->
  JR^A \o qsvt_prefix d phi t \o JR = peval B (split_pair d phi t).1.
Proof.
move=>Et; rewrite -comp_lfunA qsvt_full_column Et /even_column
  comp_lfunDr (comp_lfunA JR^A JR _) isofE comp_lfun1l
  (comp_lfunA JR^A KR _) (right_defect_orthogonal U JR JL)
  comp_lfun0l addr0.
by [].
Qed.

Corollary qsvt_odd_block d phi t : odd t = true ->
  JL^A \o qsvt_prefix d phi t \o JR = A \o peval B (split_pair d phi t).1.
Proof.
move=>Et; rewrite -comp_lfunA qsvt_full_column Et /odd_column
  comp_lfunDr (comp_lfunA JL^A (JL \o A) _) (comp_lfunA JL^A JL A)
  isofE comp_lfun1l (comp_lfunA JL^A KL _)
  (left_defect_orthogonal U JR JL) comp_lfun0l addr0.
by [].
Qed.

Theorem qsvt_complex_even d phi t : odd t = false ->
  JR^A \o qsvt_prefix d phi t \o JR = sv_even (scalar_pair d phi t).1 A.
Proof.
move=>Et; rewrite /sv_even (split_first_even d phi Et).
exact: qsvt_even_block Et.
Qed.

Theorem qsvt_complex_odd d phi t : odd t = true ->
  JL^A \o qsvt_prefix d phi t \o JR = sv_odd (scalar_pair d phi t).1 A.
Proof.
move=>Et; rewrite /sv_odd (split_first_odd d phi Et).
exact: qsvt_odd_block Et.
Qed.
End Lifting.

Section RealColumns.
Variables (H HR HL : chsType) (U : 'FU(H)).
Variables (JR : 'FI(HR,H)) (JL : 'FI(HL,H)).

Definition success_operator d phi t : 'End(H) := (2:C)^-1 *:
  ((qsvt_prefix U JR JL d phi t : 'End(H)) +
   (qsvt_prefix U JR JL d (fun j=>-phi j) t : 'End(H))).

Theorem average_even_column d phi t : odd t = false ->
  success_operator d phi t \o JR = even_column U JR JL
    (poly_real (split_pair d phi t).1) (poly_real (split_pair d phi t).2).
Proof.
move=>Et.
rewrite /success_operator -comp_lfunZl comp_lfunDl !qsvt_full_column Et
  split_pair_neg /= /even_column /poly_real !pevalZ !pevalD.
by rewrite -!comp_lfunZr !comp_lfunDr -scalerDr addrACA.
Qed.

Theorem average_odd_column d phi t : odd t = true ->
  success_operator d phi t \o JR = odd_column U JR JL
    (poly_real (split_pair d phi t).1) (poly_real (split_pair d phi t).2).
Proof.
move=>Et.
rewrite /success_operator -comp_lfunZl comp_lfunDl !qsvt_full_column Et
  split_pair_neg /= /odd_column /poly_real !pevalZ !pevalD.
by rewrite -!comp_lfunZr !comp_lfunDr -scalerDr addrACA.
Qed.

(* These are conditional scalar-to-operator theorems, not a phase-existence
   assumption: poly_real Q = 0 is an inspectable polynomial condition. *)
Theorem real_qsvt_success_even d phi t : odd t = false ->
  poly_real (scalar_pair d phi t).2 = 0 ->
  success_operator d phi t \o JR =
  JR \o sv_even (poly_real (scalar_pair d phi t).1) (encoded U JR JL).
Proof.
move=>Et Eq.
have Hb : poly_real (split_pair d phi t).2 = 0.
  by rewrite -(split_second d phi t) Et -odd_poly_real Eq odd_polyC.
rewrite (average_even_column _ _ Et) /even_column Hb peval0 comp_lfun0r addr0.
by rewrite /sv_even even_poly_real (split_first_even d phi Et).
Qed.

Theorem real_qsvt_success_odd d phi t : odd t = true ->
  poly_real (scalar_pair d phi t).2 = 0 ->
  success_operator d phi t \o JR =
  JL \o sv_odd (poly_real (scalar_pair d phi t).1) (encoded U JR JL).
Proof.
move=>Et Eq.
have Hb : poly_real (split_pair d phi t).2 = 0.
  by rewrite -(split_second d phi t) Et -even_poly_real Eq even_polyC.
rewrite (average_odd_column _ _ Et) /odd_column Hb peval0 comp_lfun0r addr0.
by rewrite /sv_odd odd_poly_real (split_first_odd d phi Et) comp_lfunA.
Qed.
End RealColumns.
Section EvaluationTransport.
Variables (H K:chsType) (B:'End(H)) (D:'End(K)) (M:'Hom(H,K)).
Lemma peval_intertwine (p:{poly C}) : M \o B = D \o M ->
  M \o peval B p = peval D p \o M.
Proof.
move=>MB; elim/poly_ind: p=>[|p a IH].
- by rewrite !peval0 comp_lfun0l comp_lfun0r.
- rewrite !pevalD !pevalM !pevalX !pevalC comp_lfunDr comp_lfunDl.
  rewrite (comp_lfunA M (peval B p) B) IH -[(_ \o M) \o B]comp_lfunA MB comp_lfunA.
  by rewrite -comp_lfunZr comp_lfun1r -comp_lfunZl comp_lfun1l.
Qed.
End EvaluationTransport.
Lemma peval_adjoint (H:chsType) (B:'End(H)) (p:{poly C}) :
  (peval B p)^A = peval B^A (QSVTPolynomial.poly_star p).
Proof.
elim/poly_ind: p=>[|p a IH].
- by rewrite QSVTPolynomial.poly_star0 !peval0 adjf0.
- rewrite QSVTPolynomial.poly_starD QSVTPolynomial.poly_starM
    QSVTPolynomial.poly_starX QSVTPolynomial.poly_starC !pevalD !pevalM
    !pevalX !pevalC adjfD adjf_comp IH adjfZ adjf1.
  by rewrite (@peval_intertwine H H B^A B^A B^A (QSVTPolynomial.poly_star p) erefl).
Qed.
Lemma sv_odd_adjoint (H K:chsType) (A:'Hom(H,K)) (p:{poly C}) :
  QSVTPolynomial.poly_star p=p -> (sv_odd p A)^A = sv_odd p A^A.
Proof.
move=>hp; rewrite /sv_odd adjf_comp peval_adjoint adjf_comp !adjfK -odd_poly_star hp.
have hi : A^A \o (A \o A^A) = (A^A \o A) \o A^A by rewrite comp_lfunA.
exact: esym (peval_intertwine _ hi).
Qed.
Lemma sv_even_adjoint (H K:chsType) (A:'Hom(H,K)) (p:{poly C}) :
  QSVTPolynomial.poly_star p=p -> (sv_even p A)^A = sv_even p A.
Proof.
by move=>hp; rewrite /sv_even peval_adjoint adjf_comp adjfK -even_poly_star hp.
Qed.

End QSVTModel.

Module QSVTWords.
Import QSVTModel.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation R := hermitian.R.
Section Words.
Variable (H : chsType).
Fixpoint qword (U : 'End(H)) (PR PL : 'FP(H)) (ps : seq R) : 'End(H) :=
  if ps is theta::ts then
    if ts is [::] then projector_phase PR theta
    else qword U^A PL PR ts \o U \o projector_phase PR theta
  else \1.
Lemma qword_cons U PR PL theta ps : ps != [::] ->
  qword U PR PL (theta::ps) =
    qword U^A PL PR ps \o U \o projector_phase PR theta.
Proof. by case: ps. Qed.
Lemma qword_rcons U PR PL ps theta : ps != [::] ->
  qword U PR PL (rcons ps theta) =
    projector_phase (if odd (size ps) then PL else PR) theta \o
      (if odd (size ps).-1 then U^A else U) \o qword U PR PL ps.
Proof.
elim: ps U PR PL=>[|a ps IH] U PR PL; first by [].
case: ps IH=>[|b ts] IH _; first by rewrite /=.
change (qword U^A PL PR (rcons (b::ts) theta) \o U \o projector_phase PR a =
  projector_phase (if odd (size (a::b::ts)) then PL else PR) theta \o
    (if odd (size (a::b::ts)).-1 then U^A else U) \o
    qword U PR PL (a::b::ts)).
rewrite (IH U^A PL PR isT) (@qword_cons U PR PL a (b::ts) isT).
by case E: (odd (size ts)); rewrite /= E ?adjfK !comp_lfunA.
Qed.
Lemma phase_adjoint (P : 'FP(H)) theta :
  (projector_phase P theta)^A = (projector_phase P (-theta) : 'End(H)).
Proof. exact: projector_phase_adjoint. Qed.

Theorem qword_adjoint U PR PL ps :
  (qword U PR PL ps)^A =
    qword (if odd (size ps).-1 then U^A else U)
      (if odd (size ps).-1 then PL else PR)
      (if odd (size ps).-1 then PR else PL)
      (rev [seq -theta | theta <- ps]).
Proof.
elim: ps U PR PL=>[|a ps IH] U PR PL; first by rewrite /= adjf1.
case: ps IH=>[|b ts] IH; first by rewrite /= phase_adjoint.
rewrite (@qword_cons U PR PL a (b::ts) isT) !adjf_comp
  phase_adjoint (IH U^A PL PR).
rewrite [in RHS]map_cons [in RHS]rev_cons.
have Hnz : rev [seq -theta | theta <- b::ts] != [::].
  by rewrite -size_eq0 size_rev size_map /=.
rewrite (qword_rcons _ _ _ _ Hnz) !size_rev !size_map.
by case E: (odd (size ts)); rewrite /= E ?adjfK !comp_lfunA.
Qed.

End Words.
Definition phase_list d (phi : nat -> R) t :=
  [seq phi (d-i)%N | i <- iota 0 t.+1].
Lemma phase_list_size d phi t : size (phase_list d phi t) = t.+1.
Proof. by rewrite /phase_list size_map size_iota. Qed.
Lemma phase_listS d phi t :
  phase_list d phi t.+1 = rcons (phase_list d phi t) (phi (d-t.+1)%N).
Proof.
by rewrite /phase_list -[t.+2]addn1 iotaD /= cats1 map_rcons add0n.
Qed.
Lemma nth_phase_list d phi t i : (i < t.+1)%N ->
  nth (0 : R) (phase_list d phi t) i = phi (d-i)%N.
Proof.
move=>Hi; rewrite /phase_list (nth_map 0) ?size_iota //.
by rewrite nth_iota // add0n.
Qed.
Lemma phase_list_reverse d phi :
  rev [seq -theta | theta <- phase_list d phi d] =
    phase_list d (fun j => -phi (d-j)%N) d.
Proof.
apply: (eq_from_nth (x0 := (0 : R))).
- by rewrite size_rev size_map !phase_list_size.
- move=>i Hi; rewrite size_rev size_map phase_list_size in Hi.
  have Hsz : size [seq -theta | theta <- phase_list d phi d] = d.+1.
    by rewrite size_map phase_list_size.
  have Hlt : (i < size [seq -theta | theta <- phase_list d phi d])%N.
    by rewrite Hsz.
  rewrite (nth_rev (0 : R) Hlt) Hsz subSS.
  have Hj : (d-i < d.+1)%N by rewrite ltnS leq_subr.
  have Hmapj : (d-i < size (phase_list d phi d))%N.
    by rewrite phase_list_size.
  rewrite (nth_map (0 : R) (0 : R) (fun theta : R => -theta) Hmapj).
  by rewrite !nth_phase_list //.

Qed.

Section PrefixBridge.
Variables (H HR HL : chsType) (U : 'FU(H)).
Variables (JR : 'FI(HR,H)) (JL : 'FI(HL,H)).
Lemma qword_qsvt_prefix d phi t :
  qword (U : 'End(H)) (range_projector JR) (range_projector JL)
    (phase_list d phi t) = (qsvt_prefix U JR JL d phi t : 'End(H)).
Proof.
elim: t=>[|t IH]; first by rewrite /phase_list /= subn0.
have Hnz : phase_list d phi t != [::].
  by rewrite -size_eq0 phase_list_size.
rewrite phase_listS (qword_rcons _ _ _ _ Hnz) phase_list_size IH.
by rewrite /=; case: (odd t).
Qed.
End PrefixBridge.

Section PrefixAdjoint.
Variables (H HR HL : chsType) (U : 'FU(H)).
Variables (JR : 'FI(HR,H)) (JL : 'FI(HL,H)).

Theorem qsvt_prefix_adjoint_even d phi : odd d = false ->
  (qsvt_prefix U JR JL d phi d)^A =
    (qsvt_prefix U JR JL d (fun j => -phi (d-j)%N) d : 'End(H)).
Proof.
move=>Hd.
rewrite -(@qword_qsvt_prefix H HR HL U JR JL d phi d)
  qword_adjoint phase_list_size /= Hd phase_list_reverse.
exact: qword_qsvt_prefix.
Qed.

Theorem qsvt_prefix_adjoint_odd d phi : odd d = true ->
  (qsvt_prefix U JR JL d phi d)^A =
    (qsvt_prefix [unitary of U^A] JL JR d (fun j => -phi (d-j)%N) d : 'End(H)).
Proof.
move=>Hd.
rewrite -(@qword_qsvt_prefix H HR HL U JR JL d phi d)
  qword_adjoint phase_list_size /= Hd phase_list_reverse.
exact: (@qword_qsvt_prefix H HL HR [unitary of U^A] JL JR).
Qed.

Theorem success_operator_adjoint_even d phi : odd d = false ->
  (success_operator U JR JL d phi d)^A =
    success_operator U JR JL d (fun j => -phi (d-j)%N) d.
Proof.
move=>Hd.
by rewrite /success_operator adjfZ adjfD rmorphV ?unitfE ?pnatr_eq0 // rmorph_nat
  (@qsvt_prefix_adjoint_even d phi Hd)
  (@qsvt_prefix_adjoint_even d (fun j => -phi j) Hd).
Qed.

Theorem success_operator_adjoint_odd d phi : odd d = true ->
  (success_operator U JR JL d phi d)^A =
    success_operator [unitary of U^A] JL JR d (fun j => -phi (d-j)%N) d.
Proof.
move=>Hd.
by rewrite /success_operator adjfZ adjfD rmorphV ?unitfE ?pnatr_eq0 // rmorph_nat
  (@qsvt_prefix_adjoint_odd d phi Hd)
  (@qsvt_prefix_adjoint_odd d (fun j => -phi j) Hd).
Qed.

End PrefixAdjoint.

End QSVTWords.

Module QSVTScalarReverse.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import QSVTModel QSVTPairAlgebra.
Local Open Scope ring_scope.
Local Notation R := hermitian.R.

Lemma canonical_phases_reverse d (phi : nat -> R) :
  [seq -phi (d-j)%N | j <- iota 0 d.+1] =
  map -%R (rev [seq phi j | j <- iota 0 d.+1]).
Proof.
apply: (@eq_from_nth _ 0).
  by rewrite !size_map size_rev size_map.
move=>i hi; rewrite size_map size_iota in hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
rewrite (nth_map 0) ?size_rev ?size_map ?size_iota //.
rewrite nth_rev ?size_map ?size_iota //.
rewrite ?size_map ?size_iota subSS.
rewrite (nth_map 0) ?size_iota ?ltnS ?leq_subr //.
by rewrite nth_iota ?ltnS ?leq_subr // add0n.
Qed.

Lemma complete_phasesE d (phi : nat -> R) :
  rcons [seq phi j | j <- iota 0 d] (phi d) =
  [seq phi j | j <- iota 0 d.+1].
Proof. by rewrite -addn1 iotaD map_cat /= add0n cats1. Qed.

Lemma scalar_pair_sequence d (phi : nat -> R) :
  scalar_pair d phi d = qsp_sequence [seq phi j | j <- iota 0 d.+1].
Proof.
by rewrite scalar_pairE phase_prefix_complete -qsp_sequence_rcons complete_phasesE.
Qed.

Theorem scalar_pair_reversal d (phi : nat -> R) :
  scalar_pair d (fun j => -phi (d-j)%N) d =
  pair_adjoint (scalar_pair d phi d).
Proof.
by rewrite !scalar_pair_sequence qsp_sequence_adjoint canonical_phases_reverse.
Qed.

End QSVTScalarReverse.

Module QSVTUniformPhase.
Import Order.LTheory GRing.Theory Num.Def Num.Theory QSVTModel.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Theorem real_polynomial_phase_witness d (p : {poly R}) :
  QSVTRealPair.admissible d p -> exists phi : nat -> R,
    poly_real (scalar_pair d phi d).1 = QSVTRealPair.r_embed p /\
    poly_real (scalar_pair d phi d).2 = 0.
Proof.
move=>ha.
have [prefix [last [hlen [hP hQ]]]] :=
  @QSVTRealPair.real_qsp_phase_witness R d p ha.
pose phi := nth 0 (rcons prefix last).
have Hpair : scalar_pair d phi d = QSVTPolynomial.qsp_pair prefix last.
  by rewrite -hlen /phi scalar_pair_from_list.
exists phi; rewrite Hpair /= /poly_real hP hQ scaler0; split=>//.
by rewrite scalerA mulVf ?pnatr_eq0 // scale1r.
Qed.
End QSVTUniformPhase.

Module QSVTRows.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import QSVTModel QSVTWords QSVTScalarReverse QSVTPolynomial QSVTPairAlgebra.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.
Lemma poly_real_star (p:{poly C}) : poly_real (poly_star p)=poly_real p.
Proof. by rewrite /poly_real poly_starK addrC. Qed.
Lemma poly_real_neg (p:{poly C}) : poly_real (poly_neg p)=poly_neg (poly_real p).
Proof. by rewrite /poly_real poly_star_neg /poly_neg comp_polyZ comp_polyD. Qed.
Lemma poly_real_fixed (p:{poly C}) : poly_star (poly_real p)=poly_real p.
Proof.
apply/polyP=>i.
rewrite poly_star_coef /poly_real !coefZ !coefD !poly_star_coef.
rewrite rmorphM rmorphV ?unitfE ?pnatr_eq0 // rmorph_nat rmorphD.
change ((2:C)^-1 * ((p`_i)^*%C + ((p`_i)^*%C)^*%C) = (2:C)^-1*(p`_i+(p`_i)^*%C)).
by rewrite conjcK addrC.
Qed.
Section Rows.
Variables (H HR HL:chsType) (U:'FU(H)).
Variables (JR:'FI(HR,H)) (JL:'FI(HL,H)).
Theorem real_qsvt_row_even d phi : odd d=false ->
 poly_real (scalar_pair d phi d).2=0 ->
 (success_operator U JR JL d phi d)^A \o JR =
 JR \o (sv_even (poly_real (scalar_pair d phi d).1) (encoded U JR JL))^A.
Proof.
move=>Hd Hq.
have Hqr : poly_real (scalar_pair d (fun j=>-phi(d-j)%N) d).2=0.
  by rewrite scalar_pair_reversal /pair_adjoint /= poly_real_neg Hq /poly_neg comp_poly0.
by rewrite (success_operator_adjoint_even U JR JL phi Hd)
 (real_qsvt_success_even U JR JL Hd Hqr)
 scalar_pair_reversal /pair_adjoint /= poly_real_star
 sv_even_adjoint // poly_real_fixed.
Qed.
Theorem real_qsvt_row_odd d phi : odd d=true ->
 poly_real (scalar_pair d phi d).2=0 ->
 (success_operator U JR JL d phi d)^A \o JL =
 JR \o (sv_odd (poly_real (scalar_pair d phi d).1) (encoded U JR JL))^A.
Proof.
move=>Hd Hq.
have Hqr : poly_real (scalar_pair d (fun j=>-phi(d-j)%N) d).2=0.
  by rewrite scalar_pair_reversal /pair_adjoint /= poly_real_neg Hq /poly_neg comp_poly0.
rewrite (success_operator_adjoint_odd U JR JL phi Hd)
 (real_qsvt_success_odd [unitary of U^A] JL JR Hd Hqr)
 scalar_pair_reversal /pair_adjoint /= poly_real_star.
rewrite sv_odd_adjoint ?poly_real_fixed //.
by rewrite /encoded !adjf_comp adjfK !comp_lfunA.
Qed.
End Rows.
End QSVTRows.

Module QSVTImaginaryColumns.
Import Order.LTheory GRing.Theory Num.Def Num.Theory QSVTModel.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition poly_imag (p : {poly C}) :=
  (-'i%C) *: ((2:C)^-1 *: (p-QSVTPolynomial.poly_star p)).

Lemma imaginary_reconstruct p :
  ('i%C : C) *: poly_imag p = (2:C)^-1 *: (p-QSVTPolynomial.poly_star p).
Proof.
rewrite /poly_imag scalerA.
have hi : ('i%C : C) * (-'i%C) = 1 by simpc.
by rewrite hi scale1r.
Qed.

Lemma even_poly_imag p : even_poly (poly_imag p) = poly_imag (even_poly p).
Proof.
by rewrite /poly_imag !linearZ !linearB /= even_poly_star
  -scalerBr !scalerA mulrC.
Qed.
Lemma odd_poly_imag p : odd_poly (poly_imag p) = poly_imag (odd_poly p).
Proof.
by rewrite /poly_imag !linearZ !linearB /= odd_poly_star
  -scalerBr !scalerA mulrC.
Qed.

Section Columns.
Variables (H HR HL : chsType) (U : 'FU(H)).
Variables (JR : 'FI(HR,H)) (JL : 'FI(HL,H)).

Definition difference_operator d phi t : 'End(H) := (2:C)^-1 *:
  ((qsvt_prefix U JR JL d phi t : 'End(H)) -
   (qsvt_prefix U JR JL d (fun j=>-phi j) t : 'End(H))).

Lemma even_column_scale a b c :
  even_column U JR JL (c*:a) (c*:b) = c*:even_column U JR JL a b.
Proof.
by rewrite /even_column !pevalZ -!comp_lfunZr -scalerDr.
Qed.
Lemma odd_column_scale a b c :
  odd_column U JR JL (c*:a) (c*:b) = c*:odd_column U JR JL a b.
Proof.
by rewrite /odd_column !pevalZ -!comp_lfunZr -scalerDr.
Qed.
Lemma even_column_sub a b c e :
  even_column U JR JL (a-c) (b-e) =
  even_column U JR JL a b - even_column U JR JL c e.
Proof.
by rewrite /even_column !pevalB !compose_subr opprD addrACA.
Qed.
Lemma odd_column_sub a b c e :
  odd_column U JR JL (a-c) (b-e) =
  odd_column U JR JL a b - odd_column U JR JL c e.
Proof.
by rewrite /odd_column !pevalB !compose_subr opprD addrACA.
Qed.

Theorem difference_even_column d phi t : odd t = false ->
  difference_operator d phi t \o JR =
  ('i%C : C) *: even_column U JR JL
    (poly_imag (split_pair d phi t).1) (poly_imag (split_pair d phi t).2).
Proof.
move=>Et.
rewrite /difference_operator -comp_lfunZl compose_subl !qsvt_full_column Et
  split_pair_neg /= -even_column_scale !imaginary_reconstruct
  even_column_scale even_column_sub.
by [].
Qed.

Theorem difference_odd_column d phi t : odd t = true ->
  difference_operator d phi t \o JR =
  ('i%C : C) *: odd_column U JR JL
    (poly_imag (split_pair d phi t).1) (poly_imag (split_pair d phi t).2).
Proof.
move=>Et.
rewrite /difference_operator -comp_lfunZl compose_subl !qsvt_full_column Et
  split_pair_neg /= -odd_column_scale !imaginary_reconstruct
  odd_column_scale odd_column_sub.
by [].
Qed.

Definition failure_column_even d phi t : 'Hom(HR,H) :=
  even_column U JR JL
    (even_poly (poly_imag (scalar_pair d phi t).1))
    (odd_poly (poly_imag (scalar_pair d phi t).2)).
Definition failure_column_odd d phi t : 'Hom(HR,H) :=
  odd_column U JR JL
    (odd_poly (poly_imag (scalar_pair d phi t).1))
    (even_poly (poly_imag (scalar_pair d phi t).2)).

Theorem explicit_failure_column_even d phi t : odd t = false ->
  difference_operator d phi t \o JR =
  ('i%C : C) *: failure_column_even d phi t.
Proof.
move=>Et; rewrite (difference_even_column _ _ Et) /failure_column_even.
by rewrite even_poly_imag odd_poly_imag
  (split_first_even d phi Et) -(split_second d phi t) Et.
Qed.
Theorem explicit_failure_column_odd d phi t : odd t = true ->
  difference_operator d phi t \o JR =
  ('i%C : C) *: failure_column_odd d phi t.
Proof.
move=>Et; rewrite (difference_odd_column _ _ Et) /failure_column_odd.
by rewrite even_poly_imag odd_poly_imag
  (split_first_odd d phi Et) -(split_second d phi t) Et.
Qed.
End Columns.

Section Density.
Variables (H K L : chsType).
Variables (J : 'FI(K,H)) (D : 'End(H)) (Gamma : 'Hom(K,H)).

Theorem encoded_success_density (Jout : 'FI(L,H)) (F : 'Hom(K,L))
    (rho : 'End(K)) :
  D \o J = Jout \o F ->
  formso D (formlf J rho) = formlf Jout (formlf F rho).
Proof.
by move=>Hcol; rewrite -formlf_soE !formlf_comp Hcol.
Qed.

Lemma imaginary_formlf (rho : 'End(K)) :
  formlf (('i%C : C) *: Gamma) rho = formlf Gamma rho.
Proof.
rewrite !formlfE adjfZ -!comp_lfunZl -!comp_lfunZr scalerA.
have hi : ('i%C : C) * ('i%C)^*%C = 1 by simpc.
by rewrite hi scale1r.
Qed.

Theorem encoded_failure_density (rho : 'End(K)) :
  D \o J = ('i%C : C) *: Gamma ->
  formso D (formlf J rho) = formlf Gamma rho.
Proof.
move=>Hcol; rewrite -!formlf_soE formlf_comp Hcol.
exact: imaginary_formlf.
Qed.
End Density.
End QSVTImaginaryColumns.

(* Rectangular SVD correspondence, retaining the full right zero subspace. *)
Module QSVTSVD.
Import QSVTModel QSVTPolynomial trigo.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.

Lemma peval_eigenvector (H : chsType) (B : 'End(H)) (v : H)
    (z : C) (p : {poly C}) :
  B v = z *: v -> peval B p v = p.[z] *: v.
Proof.
move=> Hv; elim/poly_ind: p=>[|p a IH].
- by rewrite peval0 horner0 !lfunE scale0r.
- rewrite pevalD pevalM pevalX pevalC !lfunE /=
    hornerD hornerM hornerX hornerC.
  rewrite !comp_lfunE !scale_lfunE id_lfunE Hv linearZ /= IH scalerA.
  by rewrite mulrC scalerDl.
Qed.

Lemma svd_right_gram m n (A : 'M[C]_(m,n)) :
  A^*t *m A = svd_v A *m
    diag_mx ((svd_d_exdr (svd_d A)).^+2) *m (svd_v A)^*t.
Proof.
rewrite [in LHS](svdE A) !adjmxM !adjmxK !mulmxA
  mulmxKtV // ?svd_pE //.
congr (_ *m _); rewrite -mulmxA; congr (_ *m _).
by rewrite cdiag_mx_mulr svd_diag_conj ?svd_pE // dexpmx2.
Qed.

Lemma peval_diagonal (H : chsType) (d : 'rV[C]_(dim H))
    (p : {poly C}) :
  h2mx (peval (mx2h (diag_mx d) : 'End(H)) p) =
    diag_mx (\row_j p.[d 0 j]).
Proof.
elim/poly_ind: p=>[|p a IH].
- rewrite peval0 linear0 /=; apply/matrixP=>i j.
  by rewrite !mxE horner0 mul0rn.
- rewrite pevalD pevalM pevalX pevalC linearD /= h2mx_comp
    IH mx2hK linearZ /= h2mx1 mulmx_diag.
  apply/matrixP=>i j; rewrite !mxE hornerD hornerM hornerX hornerC.
  by case: (i==j); rewrite ?mulr0 ?addr0 ?mulr1.
Qed.

Lemma peval_svd (H K : chsType) (A : 'Hom(H,K)) (p : {poly C}) :
  h2mx (peval (A^A \o A) p) = svd_v (h2mx A) *m
    diag_mx (\row_j p.[(svd_d_exdr (svd_d (h2mx A)) 0 j)^+2])
      *m (svd_v (h2mx A))^*t.
Proof.
pose V := svd_v (h2mx A).
pose ds := svd_d_exdr (svd_d (h2mx A)).
have hi : (mx2h V : 'End(H)) \o mx2h (diag_mx (ds .^+2)) =
    (A^A \o A) \o mx2h V.
  apply/h2mx_inj; rewrite !h2mx_comp h2mx_adj !mx2hK svd_right_gram.
  by rewrite mulmxKtV // ?svd_pE.
have hp := @peval_intertwine H H (mx2h (diag_mx (ds .^+2)))
  (A^A \o A) (mx2h V) p hi.
move: (congr1 (fun F : 'End(H) => h2mx F *m V^*t) hp).
rewrite !h2mx_comp !mx2hK peval_diagonal mulmxtVK // ?svd_pE.
- done.
- rewrite /V /ds; move=> <-; congr (_ *m _ *m _); congr (diag_mx _).
  apply/matrixP=>i j; by rewrite !mxE.
Qed.

Lemma sv_even_svd (H K : chsType) (A : 'Hom(H,K)) (p : {poly C}) :
  poly_parity p false ->
  h2mx (sv_even p A) = svd_v (h2mx A) *m
    diag_mx (\row_j p.[svd_d_exdr (svd_d (h2mx A)) 0 j])
      *m (svd_v (h2mx A))^*t.
Proof.
move=> hp; rewrite /sv_even peval_svd.
congr (_ *m _ *m _); congr (diag_mx _); apply/matrixP=>i j; rewrite !mxE.
by rewrite {2}(poly_parity_evenE hp) horner_comp hornerXn.
Qed.

Lemma cdiag_map_mul m n (D : 'rV[C]_(minn m n)) (f : C -> C) :
  cdiag_mx D *m diag_mx (map_mx f (svd_d_exdr D)) =
    cdiag_mx (map_mx (fun z => z * f z) D).
Proof.
apply/matrixP=>i j; rewrite mul_mx_diag !mxE /cdiag_mx /svd_d_exdr !castmxE /=.
set i' := (cast_ord (esym (min_idl m n)) i).
set j' := (cast_ord (esym (min_idr m n)) j).
case: (split_ordP i')=>a ->; case: (split_ordP j')=>b ->;
  rewrite !mxE /= ?mul0r //.
all: rewrite ?splitEl ?splitEr /= ?row_mxEl ?row_mxEr ?mxE ?mul0r //.
rewrite cast_ord_id; case: eqP=>[->|_] //.
by rewrite !mulr0n mul0r.
Qed.

Lemma sv_odd_svd (H K : chsType) (A : 'Hom(H,K)) (p : {poly C}) :
  poly_parity p true ->
  h2mx (sv_odd p A) = svd_u (h2mx A) *m
    cdiag_mx (map_mx (fun z => p.[z]) (svd_d (h2mx A)))
      *m (svd_v (h2mx A))^*t.
Proof.
move=> hp; rewrite /sv_odd h2mx_comp peval_svd
  {1}(svdE (h2mx A)) !mulmxA mulmxKtV // ?svd_pE //.
rewrite -!mulmxA; congr (_ *m _); rewrite mulmxA; congr (_ *m _).
have hd : (\row_j (odd_poly p).[(svd_d_exdr (svd_d (h2mx A)) 0 j)^+2]) =
    map_mx (fun z => (odd_poly p).[z^+2]) (svd_d_exdr (svd_d (h2mx A))).
  by apply/matrixP=>i j; rewrite !mxE ord1.
rewrite hd cdiag_map_mul; congr (cdiag_mx _); apply/matrixP=>i j; rewrite !mxE.
by rewrite {2}(poly_parity_oddE hp) hornerM horner_comp hornerXn hornerX mulrC.
Qed.

Lemma sv_even_kernel (H K : chsType) (A : 'Hom(H,K))
    (p : {poly C}) (v : H) :
  A v = 0 -> sv_even p A v = p.[0] *: v.
Proof.
move=> Hv; have HB : (A^A \o A) v = (0:C) *: v.
  by rewrite comp_lfunE Hv linear0 scale0r.
rewrite /sv_even (peval_eigenvector _ HB).
by rewrite !horner_coef0 coef_even_poly.
Qed.

Lemma sv_odd_kernel (H K : chsType) (A : 'Hom(H,K))
    (p : {poly C}) (v : H) :
  A v = 0 -> sv_odd p A v = 0.
Proof.
move=> Hv; have HB : (A^A \o A) v = (0:C) *: v.
  by rewrite comp_lfunE Hv linear0 scale0r.
by rewrite /sv_odd comp_lfunE (peval_eigenvector _ HB) linearZ /= Hv scaler0.
Qed.
End QSVTSVD.
