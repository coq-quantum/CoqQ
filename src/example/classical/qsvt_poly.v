(* Exact scalar QSP in the reflection convention of the QSVT guide.
   The forward recurrence and its converse cover normalized complex polynomial
   pairs at every nominal degree.  The remaining modules provide real
   completion factors and root/multiplicity lemmas. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect polydiv.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.reals Require Import reals.
From mathcomp.real_closed Require Import polyrcf polyorder.
From mathcomp.analysis Require Import trigo.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra.
From mathcomp Require Import ring_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module QSVTPolynomial.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex trigo.
Local Open Scope ring_scope.

Section Polynomial.
Variable R : realType.
Local Notation C := R[i].
Local Notation poly := {poly C}.

Definition degree_le (p : poly) d :=
  forall i, (d < i)%N -> p`_i = 0.
Definition degree_lt (p : poly) d :=
  forall i, (d <= i)%N -> p`_i = 0.
Definition poly_parity (p : poly) (b : bool) :=
  forall i, odd i != b -> p`_i = 0.
Definition poly_star (p : poly) := map_poly conjc p.
Definition defect : poly := 1 - 'X ^+ 2.
Definition norm_pair (p q : poly) :=
  p * poly_star p + defect * q * poly_star q.
Definition valid_pair d (p q : poly) :=
  [ /\ degree_le p d, degree_lt q d,
       poly_parity p (odd d), poly_parity q (~~ odd d) &
       norm_pair p q = 1 ].

Lemma degree_le_size p d : degree_le p d <-> (size p <= d.+1)%N.
Proof. by split=> [/leq_sizeP|/leq_sizeP]. Qed.

Lemma degree_lt_size p d : degree_lt p d <-> (size p <= d)%N.
Proof. by split=> [/leq_sizeP|/leq_sizeP]. Qed.

Lemma degree_lt0 p : degree_lt p 0 <-> p = 0.
Proof.
split=> [/degree_lt_size/size_poly_leq0P //|->].
by apply/degree_lt_size; rewrite size_poly0.
Qed.

Lemma poly_star_coef p i : (poly_star p)`_i = (p`_i)^*%C.
Proof. exact: coef_map. Qed.
Lemma poly_starK : involutive poly_star.
Proof. by move=> p; apply/polyP=> i; rewrite !poly_star_coef conjcK. Qed.
Lemma poly_star0 : poly_star 0 = 0.
Proof. exact: map_poly0. Qed.
Lemma poly_star1 : poly_star 1 = 1.
Proof. exact: rmorph1. Qed.
Lemma poly_starC c : poly_star c%:P = (c^*%C)%:P.
Proof. exact: map_polyC. Qed.
Lemma poly_starD p q : poly_star (p + q) = poly_star p + poly_star q.
Proof. exact: rmorphD. Qed.
Lemma poly_starB p q : poly_star (p - q) = poly_star p - poly_star q.
Proof. exact: rmorphB. Qed.
Lemma poly_starN p : poly_star (- p) = - poly_star p.
Proof. exact: rmorphN. Qed.
Lemma poly_starM p q : poly_star (p * q) = poly_star p * poly_star q.
Proof. exact: rmorphM. Qed.
Lemma poly_starX : poly_star 'X = 'X.
Proof. exact: map_polyX. Qed.
Lemma poly_star_defect : poly_star defect = defect.
Proof. by rewrite /defect poly_starB poly_star1 /poly_star map_polyXn. Qed.
Lemma poly_star_horner p x :
  (poly_star p).[x%:C] = (p.[x%:C])^*%C.
Proof. by rewrite /poly_star -horner_map /= oppr0. Qed.

Lemma poly_parity0 b : poly_parity 0 b.
Proof. by move=> i _; rewrite coef0. Qed.
Lemma poly_parityC c : poly_parity c%:P false.
Proof. by move=> [|i] //= _; rewrite coefC. Qed.
Lemma poly_parityD p q b :
  poly_parity p b -> poly_parity q b -> poly_parity (p + q) b.
Proof. by move=> hp hq i hi; rewrite coefD hp // hq // addr0. Qed.
Lemma poly_parityB p q b :
  poly_parity p b -> poly_parity q b -> poly_parity (p - q) b.
Proof. by move=> hp hq i hi; rewrite coefB hp // hq // subrr. Qed.
Lemma poly_parityCM c p b : poly_parity p b -> poly_parity (c%:P * p) b.
Proof. by move=> hp i hi; rewrite coefCM hp // mulr0. Qed.
Lemma poly_parityXM p b : poly_parity p b -> poly_parity ('X * p) (~~ b).
Proof.
move=> hp [|i] hi; rewrite coefXM //=; apply: hp.
by move: hi; rewrite oddS; case: b; case: (odd i).
Qed.
Lemma poly_parity_defectM p b :
  poly_parity p b -> poly_parity (defect * p) b.
Proof.
move=> hp; have he : defect * p = p - 'X * ('X * p).
  by rewrite /defect; ring.
rewrite he; apply: poly_parityB; first exact: hp.
by have := poly_parityXM (poly_parityXM hp); rewrite negbK.
Qed.

Lemma degree_lt_weaken p d e :
  (d <= e)%N -> degree_lt p d -> degree_lt p e.
Proof. by move=> de hp i ei; apply: hp; exact: leq_trans de ei. Qed.
Lemma degree_ltD p q d :
  degree_lt p d -> degree_lt q d -> degree_lt (p + q) d.
Proof. by move=> hp hq i hi; rewrite coefD hp // hq // addr0. Qed.
Lemma degree_ltB p q d :
  degree_lt p d -> degree_lt q d -> degree_lt (p - q) d.
Proof. by move=> hp hq i hi; rewrite coefB hp // hq // subrr. Qed.
Lemma degree_ltCM c p d : degree_lt p d -> degree_lt (c%:P * p) d.
Proof. by move=> hp i hi; rewrite coefCM hp // mulr0. Qed.
Lemma degree_ltXM p d : degree_lt p d -> degree_lt ('X * p) d.+1.
Proof. by move=> hp [|i] //= hi; rewrite coefXM /= hp. Qed.
Lemma degree_lt_defectM p d : degree_lt p d -> degree_lt (defect * p) d.+2.
Proof.
move=> hp; have he : defect * p = p - 'X * ('X * p).
  by rewrite /defect; ring.
rewrite he; apply: degree_ltB; last exact: degree_ltXM (degree_ltXM hp).
exact: degree_lt_weaken (leq_trans (leqnSn d) (leqnSn d.+1)) hp.
Qed.

(* MathComp already provides the coefficient-selected even and odd parts. *)
Lemma poly_parity_evenE p :
  poly_parity p false -> p = even_poly p \Po 'X^2.
Proof.
move=> hp; have hz : odd_poly p = 0.
  by apply/polyP=> i; rewrite coef_odd_poly coef0 hp // oddS odd_double.
have h := poly_even_odd p.
by rewrite hz comp_poly0 mul0r addr0 in h; exact: esym h.
Qed.
Lemma poly_parity_oddE p :
  poly_parity p true -> p = (odd_poly p \Po 'X^2) * 'X.
Proof.
move=> hp; have hz : even_poly p = 0.
  by apply/polyP=> i; rewrite coef_even_poly coef0 hp // odd_double.
have h := poly_even_odd p.
by rewrite hz comp_poly0 add0r in h; exact: esym h.
Qed.
Lemma even_poly_compX2 (p : poly) : even_poly (p \Po 'X^2) = p.
Proof.
apply/polyP=> i; rewrite coef_even_poly coef_comp_poly_Xn // -muln2.
by rewrite dvdn_mull ?dvdnn // mulnK.
Qed.
Lemma compX2_inj : injective (fun p : poly => p \Po 'X^2).
Proof.
by move=> p q /(congr1 (fun r : poly => even_poly r)); rewrite !even_poly_compX2.
Qed.
Lemma odd_compX2_inj : injective (fun p : poly => (p \Po 'X^2) * 'X).
Proof.
move=> p q /(congr1 (fun r : poly => odd_poly r)); rewrite !odd_polyMX !even_poly_compX2.
by [].
Qed.

(* A nonempty phase sequence is represented by its prefix and final phase.
   Both components on the right of qsp_step use the old pair. *)
Definition qsp_step (phi : R) (pq : poly * poly) :=
  ((expi phi)%:P * ('X * pq.1 + defect * pq.2),
   ((expi phi)^*%C)%:P * (pq.1 - 'X * pq.2)).

Fixpoint qsp_pair (prefix : seq R) (last : R) : poly * poly :=
  if prefix is phi :: tail then qsp_step phi (qsp_pair tail last)
  else ((expi last)%:P, 0).

Lemma expi_conj (phi : R) : (expi phi)^*%C = expi (- phi).
Proof. by rewrite /expi cosN sinN. Qed.
Lemma expi_unit (phi : R) : expi phi * (expi phi)^*%C = 1.
Proof. by rewrite expi_conj -expiD addrN expi0. Qed.

Lemma qsp_step_norm phi p q :
  norm_pair (qsp_step phi (p, q)).1 (qsp_step phi (p, q)).2 =
  norm_pair p q.
Proof.
change (norm_pair ((expi phi)%:P * ('X * p + defect * q))
  (((expi phi)^*%C)%:P * (p - 'X * q)) = norm_pair p q).
rewrite /norm_pair.
rewrite !(poly_starM, poly_starB, poly_starD, poly_starN, poly_starC, poly_starX,
  poly_star_defect, conjcK).
have unitc : (expi phi)%:P * ((expi phi)^*%C)%:P = (1 : poly).
  by rewrite -polyCM expi_unit.
transitivity ((expi phi)%:P * ((expi phi)^*%C)%:P *
  (('X * p + defect * q) * ('X * poly_star p + defect * poly_star q) +
   defect * (p - 'X * q) * (poly_star p - 'X * poly_star q))).
  by ring.
rewrite unitc mul1r.
rewrite /defect; ring.
Qed.

Definition qsp_peel (phi : R) (pq : poly * poly) :=
  ('X * ((expi phi)^*%C)%:P * pq.1 + defect * (expi phi)%:P * pq.2,
   ((expi phi)^*%C)%:P * pq.1 - 'X * (expi phi)%:P * pq.2).

Lemma qsp_step_peel phi p q : qsp_step phi (qsp_peel phi (p, q)) = (p, q).
Proof.
have unitc : (expi phi)%:P * ((expi phi)^*%C)%:P = (1 : poly).
  by rewrite -polyCM expi_unit.
rewrite /qsp_step /qsp_peel; cbn [fst snd]; congr (_, _).
- transitivity ((expi phi)%:P * ((expi phi)^*%C)%:P * p).
    by rewrite /defect; ring.
  by rewrite unitc mul1r.
- transitivity ((expi phi)%:P * ((expi phi)^*%C)%:P * q).
    by rewrite /defect; ring.
  by rewrite unitc mul1r.
Qed.

Lemma qsp_peel_norm phi p q :
  norm_pair (qsp_peel phi (p, q)).1 (qsp_peel phi (p, q)).2 = norm_pair p q.
Proof.
have h := qsp_step_norm phi (qsp_peel phi (p, q)).1 (qsp_peel phi (p, q)).2.
have he : ((qsp_peel phi (p, q)).1, (qsp_peel phi (p, q)).2) =
  qsp_peel phi (p, q) by case: (qsp_peel phi (p, q)).
by rewrite he qsp_step_peel in h; exact: esym h.
Qed.

Lemma qsp_pair_norm prefix last :
  norm_pair (qsp_pair prefix last).1 (qsp_pair prefix last).2 = 1.
Proof.
elim: prefix=> [|phi tail IH] /=; last by rewrite qsp_step_norm.
by rewrite /norm_pair poly_starC poly_star0 !mulr0 addr0 -polyCM expi_unit.
Qed.

Lemma qsp_step_valid phi d p q :
  valid_pair d p q ->
  valid_pair d.+1 (qsp_step phi (p, q)).1 (qsp_step phi (p, q)).2.
Proof.
move=> [hp hq hpp hqq hn]; constructor.
- apply: degree_ltCM; apply: degree_ltD.
  + exact: degree_ltXM hp.
  + exact: degree_lt_defectM hq.
- apply: degree_ltCM; apply: degree_ltB; first exact: hp.
  exact: degree_ltXM hq.
- rewrite oddS; apply: poly_parityCM; apply: poly_parityD.
  + exact: poly_parityXM hpp.
  + exact: poly_parity_defectM hqq.
- rewrite oddS negbK; apply: poly_parityCM; apply: poly_parityB; first exact: hpp.
  by have := poly_parityXM hqq; rewrite negbK.
- by rewrite qsp_step_norm.
Qed.

Theorem qsp_pair_valid prefix last :
  valid_pair (size prefix) (qsp_pair prefix last).1 (qsp_pair prefix last).2.
Proof.
elim: prefix=> [|phi tail IH] /=; last exact: qsp_step_valid IH.
constructor.
- apply/degree_le_size; exact: size_polyC_leq1.
- by apply/degree_lt0.
- exact: poly_parityC.
- exact: poly_parity0.
- exact: qsp_pair_norm [::] last.
Qed.

Lemma norm_pair_horner p q x :
  (norm_pair p q).[x%:C] =
  p.[x%:C] * (p.[x%:C])^*%C +
    (1 - (x%:C)^+2) * q.[x%:C] * (q.[x%:C])^*%C.
Proof.
by rewrite /norm_pair /defect !(hornerD, hornerN, hornerM,
  horner_exp, hornerX, hornerC, poly_star_horner).
Qed.

Corollary qsp_pair_scalar_normalization prefix last x :
  let pq := qsp_pair prefix last in
  pq.1.[x%:C] * (pq.1.[x%:C])^*%C +
    (1 - (x%:C)^+2) * pq.2.[x%:C] * (pq.2.[x%:C])^*%C = 1.
Proof.
have h := congr1 (fun r : poly => r.[x%:C]) (qsp_pair_norm prefix last).
rewrite norm_pair_horner hornerC in h.
exact: h.
Qed.

Lemma qsp_step_neg (phi : R) p q :
  qsp_step (- phi) (poly_star p, poly_star q) =
  (poly_star (qsp_step phi (p,q)).1, poly_star (qsp_step phi (p,q)).2).
Proof.
rewrite /qsp_step; cbn [fst snd].
rewrite !(poly_starM, poly_starB, poly_starD, poly_starN, poly_starC,
  poly_starX, poly_star_defect, conjcK).
by rewrite -expi_conj conjcK.
Qed.

Lemma qsp_pair_neg prefix last :
  qsp_pair (map -%R prefix) (- last) =
  (poly_star (qsp_pair prefix last).1, poly_star (qsp_pair prefix last).2).
Proof.
elim: prefix=> [|phi tail IH].
- change (((expi (- last))%:P, 0) = (poly_star (expi last)%:P, poly_star 0)).
  by rewrite poly_starC poly_star0 -expi_conj.
- change (qsp_step (- phi) (qsp_pair (map -%R tail) (- last)) =
    (poly_star (qsp_step phi (qsp_pair tail last)).1,
     poly_star (qsp_step phi (qsp_pair tail last)).2)).
  rewrite IH; case: (qsp_pair tail last)=>p q; exact: qsp_step_neg.
Qed.

End Polynomial.
End QSVTPolynomial.

(* Algebraic factors for the real completion construction.  The root-orbit
   assembly and the full interval completion theorem remain separate. *)
Module QSVTCompletion.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Local Open Scope ring_scope.

Section Completion.
Variable R : realType.
Local Notation poly := {poly R}.

Definition completion_defect : poly := 1 - 'X ^+ 2.
Definition completion_norm (B C : poly) :=
  B ^+ 2 + completion_defect * C ^+ 2.
Definition completion_product (bc de : poly * poly) :=
  (bc.1 * de.1 - completion_defect * bc.2 * de.2,
   bc.1 * de.2 + bc.2 * de.1).

Lemma completion_product_norm B C D E :
  completion_norm (completion_product (B,C) (D,E)).1
                  (completion_product (B,C) (D,E)).2 =
  completion_norm B C * completion_norm D E.
Proof. rewrite /completion_norm /completion_product /=; ring. Qed.

Lemma completion_norm0 : completion_norm 0 0 = 0.
Proof. by rewrite /completion_norm expr0n // !mulr0 addr0. Qed.

Lemma completion_norm_constant (K : R) :
  completion_norm K%:P 0 = (K ^+ 2)%:P.
Proof. by rewrite /completion_norm expr0n // mulr0 addr0 -polyC_exp. Qed.

Lemma completion_norm_padding : completion_norm 'X 1 = 1.
Proof. rewrite /completion_norm /completion_defect; ring. Qed.

Definition completion_pad_step (bc : poly * poly) :=
  completion_product bc ('X, 1).

Fixpoint completion_padding (n : nat) (bc : poly * poly) :=
  if n is k.+1 then completion_pad_step (completion_padding k bc) else bc.

Lemma completion_padding_norm n B C :
  completion_norm (completion_padding n (B,C)).1
                  (completion_padding n (B,C)).2 = completion_norm B C.
Proof.
elim: n => [//|n IH] /=.
rewrite /completion_pad_step [completion_padding n (B,C)]surjective_pairing.
by rewrite completion_product_norm completion_norm_padding mulr1.
Qed.

Lemma completion_real_factor (s : R) (hs : 1 <= s) :
  completion_norm ((Num.sqrt (s ^+ 2 - 1))%:P * 'X) s%:P =
  (s ^+ 2)%:P - 'X ^+ 2.
Proof.
have hs2 : 0 <= s ^+ 2 - 1.
  by rewrite subr_ge0; exact: exprn_ege1 hs.
rewrite /completion_norm /completion_defect !exprMn -!polyC_exp
  (sqr_sqrtr hs2) polyCB polyC1.
ring.
Qed.

Lemma completion_imaginary_factor (t : R) :
  completion_norm ((Num.sqrt (1 + t ^+ 2))%:P * 'X) t%:P =
  'X ^+ 2 + (t ^+ 2)%:P.
Proof.
have ht : 0 <= 1 + t ^+ 2 by rewrite addr_ge0 ?ler01 ?sqr_ge0.
rewrite /completion_norm /completion_defect !exprMn -!polyC_exp
  (sqr_sqrtr ht) polyCD polyC1.
ring.
Qed.

Lemma completion_quartet_identity (u v gamma : R)
    (hgamma : gamma ^+ 2 - 2 * (u ^+ 2 + v ^+ 2) * gamma =
      1 + 2 * (v ^+ 2 - u ^+ 2))
    (hgamma0 : 0 <= gamma ^+ 2 - 1) :
  completion_norm
    (gamma%:P * 'X ^+ 2 - (u ^+ 2 + v ^+ 2)%:P)
    ((Num.sqrt (gamma ^+ 2 - 1))%:P * 'X) =
    'X ^+ 4 + (2 * (v ^+ 2 - u ^+ 2))%:P * 'X ^+ 2 +
    ((u ^+ 2 + v ^+ 2) ^+ 2)%:P.
Proof.
rewrite /completion_norm /completion_defect !exprMn -!polyC_exp
  (sqr_sqrtr hgamma0).
have hgamma2 := congr1
  (fun z => z + 2 * (u ^+ 2 + v ^+ 2) * gamma) hgamma.
rewrite subrK in hgamma2.
have hgammaP := congr1 (@polyC R) hgamma2.
ring: hgammaP.
Qed.

Definition completion_delta (u v : R) :=
  (u ^+ 2 + v ^+ 2 - 1) ^+ 2 + 4 * v ^+ 2.
Definition completion_gamma (u v : R) :=
  u ^+ 2 + v ^+ 2 + Num.sqrt (completion_delta u v).

Lemma completion_delta_ge0 u v : 0 <= completion_delta u v.
Proof.
rewrite /completion_delta; apply: addr_ge0; first exact: sqr_ge0.
by apply: mulr_ge0; [rewrite ler0n | rewrite sqr_ge0].
Qed.

Lemma completion_gamma_ge1 u v : 1 <= completion_gamma u v.
Proof.
set T := u ^+ 2 + v ^+ 2.
have hDelta : (1 - T) ^+ 2 <= completion_delta u v.
  have hsq : (1 - T) ^+ 2 = (T - 1) ^+ 2 by ring.
  rewrite hsq /completion_delta -/T lerDl.
  by apply: mulr_ge0; [rewrite ler0n | rewrite sqr_ge0].
have hnorm : `|1 - T| <= Num.sqrt (completion_delta u v).
  by rewrite -sqrtr_sqr; exact: ler_wsqrtr hDelta.
have hbound := le_trans (ler_norm (1 - T)) hnorm.
have hsum := lerD (lexx T) hbound.
have hcancel : T + (1 - T) = 1 by ring.
by rewrite hcancel in hsum.
Qed.

Lemma completion_gamma_equation u v :
  (completion_gamma u v) ^+ 2 -
      2 * (u ^+ 2 + v ^+ 2) * completion_gamma u v =
  1 + 2 * (v ^+ 2 - u ^+ 2).
Proof.
set T := u ^+ 2 + v ^+ 2.
have hroot : (completion_gamma u v - T) ^+ 2 = completion_delta u v.
  rewrite /completion_gamma -/T addrAC subrr add0r.
  exact: sqr_sqrtr (completion_delta_ge0 u v).
have halg : (completion_gamma u v) ^+ 2 - 2 * T * completion_gamma u v =
    (completion_gamma u v - T) ^+ 2 - T ^+ 2 by ring.
rewrite -/T halg hroot /completion_delta -/T /T; ring.
Qed.

Lemma completion_quartet_factor (u v : R) :
  completion_norm
    ((completion_gamma u v)%:P * 'X ^+ 2 - (u ^+ 2 + v ^+ 2)%:P)
    ((Num.sqrt ((completion_gamma u v) ^+ 2 - 1))%:P * 'X) =
    'X ^+ 4 + (2 * (v ^+ 2 - u ^+ 2))%:P * 'X ^+ 2 +
    ((u ^+ 2 + v ^+ 2) ^+ 2)%:P.
Proof.
apply: completion_quartet_identity; first exact: completion_gamma_equation.
by rewrite subr_ge0; exact: exprn_ege1 (completion_gamma_ge1 u v).
Qed.

End Completion.

Section RootMultiplicity.
Variables (F K : fieldType) (f : {rmorphism F -> K}).

Lemma multiplicity_map (p : {poly F}) (x : F) : p != 0 ->
  mup (f x) (map_poly f p) = mup x p.
Proof.
move=> hp.
have hmap : map_poly f p != 0 by rewrite map_poly_eq0.
have h n : (n <= mup (f x) (map_poly f p))%N = (n <= mup x p)%N.
  rewrite !mup_geq // -map_polyXsubC -rmorphXn.
  exact: dvdp_map.
apply/eqP; rewrite eqn_leq.
by rewrite -[(mup (f x) (map_poly f p) <= mup x p)%N]h
  [(mup x p <= mup (f x) (map_poly f p))%N]h !leqnn.
Qed.

End RootMultiplicity.

Section NegationMultiplicity.
Variable F : fieldType.

Lemma dvdp_negated_power (d p : {poly F}) n :
  (((-d) ^+ n) %| p) = ((d ^+ n) %| p).
Proof.
rewrite exprNn -signr_odd.
by case: odd; rewrite /= ?mul1r ?mulN1r ?dvdpNl.
Qed.

Lemma root_neg_multiplicity (p : {poly F}) (z : F) :
  p != 0 -> p \Po (- 'X) = p -> mup (-z) p = mup z p.
Proof.
move=> hp heven.
have hdiv x n : (('X - x%:P) ^+ n %| p) ->
    (('X - (-x)%:P) ^+ n %| p).
  move=> h.
  have hc := dvdp_comp_poly (- 'X) h.
  rewrite heven rmorphXn in hc.
  change (is_true ((('X - x%:P) \Po (- 'X)) ^+ n %| p)) in hc.
  rewrite comp_polyB comp_polyX comp_polyC in hc.
  have hfactor : -'X - x%:P = -('X - (-x)%:P) by rewrite polyCN; ring.
  by rewrite hfactor dvdp_negated_power in hc.
have h n : (n <= mup (-z) p)%N = (n <= mup z p)%N.
  rewrite !mup_geq //; apply/idP/idP.
    by move/(hdiv (-z)); rewrite opprK.
  move=> hd; exact: (@hdiv z n hd).
apply/eqP; rewrite eqn_leq.
by rewrite -[(mup (-z) p <= mup z p)%N]h [(mup z p <= mup (-z) p)%N]h !leqnn.
Qed.

End NegationMultiplicity.

Section ComplexRoots.
Variable R : realType.

Lemma root_conj_multiplicity (p : {poly R[i]}) (z : R[i]) :
  p != 0 -> map_poly conjc p = p -> mup z^*%C p = mup z p.
Proof.
move=> hp hreal.
by move: (multiplicity_map conjc z hp); rewrite hreal.
Qed.

End ComplexRoots.
End QSVTCompletion.

Module QSVTUnitCircle.
Import trigo.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Local Open Scope ring_scope.

Section Phase.
Variable R : realType.

Lemma expi_surjective (z : R[i]) : z * z^*%C = 1 ->
  exists phi : R, expi phi = z.
Proof.
case: z => a b hu.
have hab : a ^+ 2 + b ^+ 2 = 1.
  move: hu; simpc => hu.
  by move: (congr1 (@Re R) hu); rewrite /= -!expr2.
have ha2 : a ^+ 2 <= 1.
  rewrite -hab lerDl; exact: sqr_ge0.
have ha_norm : `|a| <= 1.
  rewrite -[1]sqrtr1 -[ `|a| ]sqrtr_sqr.
  exact: ler_wsqrtr ha2.
have ha_interval : -1 <= a <= 1 by rewrite -ler_norml.
have hcos : cos (acos a) = a := (acos_def ha_interval).2.
have hb2 : 1 - a ^+ 2 = b ^+ 2.
  by rewrite -hab addrAC subrr add0r.
case: (lerP 0 b) => hb.
  exists (acos a).
  by rewrite /expi hcos sin_acos // hb2 sqrtr_sqr ger0_norm.
exists (- acos a).
by rewrite /expi cosN sinN hcos sin_acos // hb2 sqrtr_sqr
  (ler0_norm (ltW hb)) opprK.
Qed.

Lemma expi_double_surjective (z : R[i]) : z * z^*%C = 1 ->
  exists phi : R, expi (phi + phi) = z.
Proof.
move/expi_surjective=> [theta htheta].
exists (theta / 2).
have hhalf : theta / 2 + theta / 2 = theta.
  by rewrite -mulr2n -mulr_natr divfK ?pnatr_eq0.
by rewrite hhalf.
Qed.

End Phase.
End QSVTUnitCircle.

Module QSVTRootEven.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Local Open Scope ring_scope.

Section Roots.
Variable R : realType.

Lemma multiplicity_mup (p : {poly R}) (r : R) :
  p != 0 -> mup r p = multiplicity r p.
Proof.
move=> hp; case: (mu_spec r hp) => q hq hpE.
by rewrite {1}hpE mupMr // mup_XsubCX eqxx.
Qed.

Lemma interior_root_even (p : {poly R}) (r : R) :
  p != 0 -> -1 < r < 1 ->
  (forall x, -1 <= x <= 1 -> 0 <= p.[x]) ->
  ~~ odd (mup r p).
Proof.
move=> hp /andP[hrN1 hr1] hnonneg.
have [yr hyr] := @neighpr_wit R p r 1 hr1 hp.
have [yl hyl] := @neighpl_wit R p (-1) r hrN1 hp.
have hyr0 : r < yr by rewrite (itvP hyr).
have hyr1 : yr < 1.
  apply: lt_le_trans (_ : next_root p r 1 <= 1).
    by rewrite (itvP hyr).
  have hnr := next_root_in p r 1.
  rewrite (max_l (ltW hr1)) in hnr.
  by rewrite (itvP hnr).
have hyl0 : -1 < yl.
  have hprN : -1 <= prev_root p (-1) r.
    have hpr := prev_root_in p (-1) r.
    rewrite (min_l (ltW hrN1)) in hpr.
    by rewrite (itvP hpr).
  have hpry : prev_root p (-1) r < yl by rewrite (itvP hyl).
  exact: le_lt_trans hprN hpry.
have hyl1 : yl < r by rewrite (itvP hyl).
have hyri : -1 <= yr <= 1.
  apply/andP; split; last exact: ltW hyr1.
  exact: le_trans (ltW hrN1) (ltW hyr0).
have hyli : -1 <= yl <= 1.
  apply/andP; split; first exact: ltW hyl0.
  exact: le_trans (ltW hyl1) (ltW hr1).
have hpyr : 0 < p.[yr].
  rewrite lt_def; apply/andP; split; last exact: hnonneg hyri.
  exact: neighpr_root hyr.
have hpyl : 0 < p.[yl].
  rewrite lt_def; apply/andP; split; last exact: hnonneg hyli.
  exact: neighpl_root hyl.
have hsr : sgp_right p r = 1.
  rewrite -(@sgr_neighpr R 1 p r yr hyr).
  exact: gtr0_sg hpyr.
have hsl := @sgr_neighpl R (-1) p r yl hyl.
rewrite (gtr0_sg hpyl) hsr mulr1 -multiplicity_mup // in hsl.
apply/negP=> ho.
rewrite ho expr1 in hsl.
have hN11 : (-1 : R) < 1 := lt_trans (@ltrN10 R) (@ltr01 R).
by rewrite -hsl ltxx in hN11.
Qed.

Lemma nonnegative_factor_quotient (f q : {poly R}) :
  f != 0 ->
  (forall x, -1 <= x <= 1 -> 0 <= f.[x]) ->
  (forall x, -1 <= x <= 1 -> 0 <= f.[x] * q.[x]) ->
  forall x, -1 <= x <= 1 -> 0 <= q.[x].
Proof.
move=> hf hfn hprod x /andP[hxN1 hx1].
rewrite leNgt; apply/negP=> hqx.
have hq : q != 0.
  apply/negP=> /eqP hq0.
  by rewrite hq0 horner0 ltxx in hqx.
have hcontr y (hy : -1 <= y <= 1) (hfy : f.[y] != 0)
    (hsg : Num.sg q.[y] = Num.sg q.[x]) : False.
  have hfypos : 0 < f.[y] by rewrite lt_def hfy hfn.
  have hqyneg : q.[y] < 0.
    rewrite -sgr_lt0 hsg (ltr0_sg hqx); exact: ltrN10.
  have hnegative : f.[y] * q.[y] < 0.
    have hqyn : 0 < - q.[y] by rewrite oppr_gt0.
    have hh := mulr_gt0 hfypos hqyn.
    by rewrite mulrN oppr_gt0 in hh.
  have hbad := le_lt_trans (hprod y hy) hnegative.
  by rewrite ltxx in hbad.
have [hx|hx] := eqVneq x 1.
  subst x.
  have hN11 : (-1 : R) < 1 := lt_trans (@ltrN10 R) (@ltr01 R).
  have [y hy] := @neighpl_wit R (f * q) (-1) 1 hN11 (mulf_neq0 hf hq).
  have /andP[hyf hyq] : y \in [predI neighpl f (-1) 1 & neighpl q (-1) 1].
    by rewrite -neighpl_mul.
  have hyl : -1 < y.
    have hprev : -1 <= prev_root (f * q) (-1) 1.
      have hin := prev_root_in (f * q) (-1) 1.
      rewrite (min_l (ltW hN11)) in hin; by rewrite (itvP hin).
    have hpy : prev_root (f * q) (-1) 1 < y by rewrite (itvP hy).
    exact: le_lt_trans hprev hpy.
  have hyu : y < 1 by rewrite (itvP hy).
  apply: (@hcontr y _ _ _).
  - by rewrite (ltW hyl) (ltW hyu).
  - exact: neighpl_root hyf.
  - have hrootq : ~~ root q 1 by rewrite /root (lt_eqF hqx).
    exact: (@sgr_neighplN R q (-1) 1 hrootq y hyq).
have hxlt : x < 1 by rewrite lt_def eq_sym hx hx1.
have [y hy] := @neighpr_wit R (f * q) x 1 hxlt (mulf_neq0 hf hq).
have /andP[hyf hyq] : y \in [predI neighpr f x 1 & neighpr q x 1].
  by rewrite -neighpr_mul.
have hyl : x < y by rewrite (itvP hy).
have hyu : y < 1.
  have hnext : next_root (f * q) x 1 <= 1.
    have hin := next_root_in (f * q) x 1.
    rewrite (max_l (ltW hxlt)) in hin; by rewrite (itvP hin).
  have hyn : y < next_root (f * q) x 1 by rewrite (itvP hy).
  exact: lt_le_trans hyn hnext.
apply: (@hcontr y _ _ _).
- apply/andP; split; last exact: ltW hyu.
  exact: le_trans hxN1 (ltW hyl).
- exact: neighpr_root hyf.
- have hrootq : q.[x] != 0 by rewrite (lt_eqF hqx).
  exact: (@sgr_neighprN R q x 1 hrootq y hyq).
Qed.

End Roots.
End QSVTRootEven.


Module QSVTCompletionReduction.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Local Open Scope ring_scope.

Section EvenQuotients.
Variable K : fieldType.

Lemma even_quotient (p f q : {poly K}) :
  f != 0 -> f \Po (- 'X) = f -> p \Po (- 'X) = p ->
  p = f * q -> q \Po (- 'X) = q.
Proof.
move=> hf hfe hpe hp.
apply: (mulfI hf).
have he := congr1 (fun r : {poly K} => r \Po (- 'X)) hp.
rewrite comp_polyM hfe hpe hp in he.
exact: esym he.
Qed.

Lemma even_divisor_quotient (p f : {poly K}) :
  f != 0 -> f \Po (- 'X) = f -> p \Po (- 'X) = p ->
  f %| p -> (p %/ f) \Po (- 'X) = p %/ f.
Proof.
move=> hf hfe hpe hdiv.
apply: (@even_quotient p f (p %/ f) hf hfe hpe).
by rewrite mulrC divpK.
Qed.

End EvenQuotients.
End QSVTCompletionReduction.

Module QSVTPairAlgebra.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex trigo.
Import QSVTPolynomial.
Local Open Scope ring_scope.
Section Algebra.
Variable R : realType.
Local Notation C := R[i].
Local Notation poly := {poly C}.
Local Notation h := (defect R).

Definition poly_neg (p : poly) := p \Po (- 'X).
Lemma poly_negD p q : poly_neg (p+q) = poly_neg p + poly_neg q.
Proof. exact: comp_polyD. Qed.
Lemma poly_negM p q : poly_neg (p*q) = poly_neg p * poly_neg q.
Proof. exact: comp_polyM. Qed.
Lemma poly_negC (c : C) : poly_neg c%:P = c%:P.
Proof. exact: comp_polyC. Qed.
Lemma poly_negX : poly_neg 'X = - 'X.
Proof. exact: comp_polyX. Qed.
Lemma poly_negN p : poly_neg (-p) = -poly_neg p.
Proof. exact: raddfN. Qed.
Lemma poly_negK : involutive poly_neg.
Proof.
move=> p; rewrite /poly_neg -comp_polyA.
have he : (- 'X : poly) \Po (- 'X) = 'X by rewrite raddfN /= comp_polyX opprK.
by rewrite he comp_polyXr.
Qed.
Lemma poly_neg_defect : poly_neg h = h.
Proof.
by rewrite /poly_neg /defect comp_polyB comp_polyC comp_Xn_poly sqrrN.
Qed.
Lemma poly_star_neg p : poly_star (poly_neg p) = poly_neg (poly_star p).
Proof. by rewrite /poly_star /poly_neg map_comp_poly rmorphN /= map_polyX. Qed.

Definition pair_product (pq rs : poly*poly) :=
  (pq.1*rs.1 + h*poly_neg (poly_star pq.2)*rs.2,
   pq.2*rs.1 + poly_neg (poly_star pq.1)*rs.2).
Definition pair_adjoint (pq : poly*poly) := (poly_star pq.1, poly_neg pq.2).
Definition pair_one : poly*poly := (1,0).
Definition phase_pair (phi : R) : poly*poly := ((expi phi)%:P,0).
Definition reflection_pair : poly*poly := ('X,1).

Lemma pair_productA : associative pair_product.
Proof.
move=> [p q] [r s] [u v]; rewrite /pair_product; cbn [fst snd]; congr (_, _);
rewrite !(poly_starM, poly_starD, poly_star_defect, poly_negM, poly_negD,
  poly_star_neg, poly_starK, poly_negK, poly_neg_defect); ring.
Qed.

Lemma pair_adjointM pq rs :
  pair_adjoint (pair_product pq rs) = pair_product (pair_adjoint rs) (pair_adjoint pq).
Proof.
case: pq=>p q; case: rs=>r s; rewrite /pair_adjoint /pair_product;
cbn [fst snd]; congr (_, _);
rewrite !(poly_starM, poly_starD, poly_star_defect, poly_negM, poly_negD,
  poly_star_neg, poly_starK, poly_negK, poly_neg_defect); ring.
Qed.

Lemma pair_adjointK : involutive pair_adjoint.
Proof. by move=> [p q]; rewrite /pair_adjoint /= poly_starK poly_negK. Qed.
Lemma pair_adjoint_phase phi : pair_adjoint (phase_pair phi) = phase_pair (-phi).
Proof.
rewrite /pair_adjoint /phase_pair; cbn [fst snd].
by rewrite poly_starC -expi_conj /poly_neg comp_poly0.
Qed.
Lemma pair_adjoint_reflection : pair_adjoint reflection_pair = reflection_pair.
Proof.
rewrite /pair_adjoint /reflection_pair; cbn [fst snd].
by rewrite poly_starX /poly_neg comp_polyC.
Qed.

Lemma qsp_step_product phi pq :
  qsp_step phi pq = pair_product (phase_pair phi) (pair_product reflection_pair pq).
Proof.
case: pq=>p q; rewrite /qsp_step /pair_product /phase_pair /reflection_pair;
cbn [fst snd].
rewrite !(poly_star0, poly_star1, poly_starC, poly_starX,
  poly_negC, poly_negX); congr (_, _); ring.
Qed.

Lemma poly_neg0 : poly_neg 0 = 0.
Proof. exact: comp_poly0. Qed.
Lemma poly_neg1 : poly_neg 1 = 1.
Proof. exact: comp_polyC. Qed.
Lemma pair_product1l : left_id pair_one pair_product.
Proof.
move=> [p q]; rewrite /pair_product /pair_one; cbn [fst snd].
by rewrite !(poly_star0, poly_star1, poly_neg0, poly_neg1,
  mul0r, mulr0, mul1r, add0r, addr0).
Qed.
Lemma pair_product1r : right_id pair_one pair_product.
Proof.
move=> [p q]; rewrite /pair_product /pair_one; cbn [fst snd].
by rewrite !mulr1 !mulr0 !addr0.
Qed.
Lemma pair_adjoint1 : pair_adjoint pair_one = pair_one.
Proof. by rewrite /pair_adjoint /pair_one /= poly_star1 poly_neg0. Qed.

Definition pair_fold (pairs : seq (poly*poly)) := foldr pair_product pair_one pairs.
Lemma pair_fold_cat pairs1 pairs2 :
  pair_fold (pairs1 ++ pairs2) = pair_product (pair_fold pairs1) (pair_fold pairs2).
Proof.
elim: pairs1=> [|pq tail IH].
- change (pair_fold pairs2 = pair_product pair_one (pair_fold pairs2)).
  by rewrite pair_product1l.
- change (pair_product pq (pair_fold (tail ++ pairs2)) =
    pair_product (pair_product pq (pair_fold tail)) (pair_fold pairs2)).
  by rewrite IH pair_productA.
Qed.
Lemma pair_fold_rcons pairs pq :
  pair_fold (rcons pairs pq) = pair_product (pair_fold pairs) pq.
Proof. by rewrite -cats1 pair_fold_cat /pair_fold /= pair_product1r. Qed.
Lemma pair_fold_adjoint pairs :
  pair_adjoint (pair_fold pairs) = pair_fold (map pair_adjoint (rev pairs)).
Proof.
elim: pairs=> [|pq tail IH]; first by rewrite /pair_fold /= pair_adjoint1.
change (pair_adjoint (pair_product pq (pair_fold tail)) =
  pair_fold (map pair_adjoint (rev (pq :: tail)))).
by rewrite pair_adjointM rev_cons map_rcons pair_fold_rcons IH.
Qed.

Fixpoint phase_factors (phases : seq R) : seq (poly*poly) :=
  if phases is phi :: tail then
    phase_pair phi :: (if tail is [::] then [::]
                       else reflection_pair :: phase_factors tail)
  else [::].

Lemma phase_factors_rcons phases phi :
  phase_factors (rcons phases phi) =
  if phases is [::] then [:: phase_pair phi]
  else rcons (rcons (phase_factors phases) reflection_pair) (phase_pair phi).
Proof.
elim: phases=> [|a tail IH]; first by [].
case: tail IH=> [|b tail] IH; first by [].
change (phase_pair a :: reflection_pair :: phase_factors (rcons (b::tail) phi) =
  phase_pair a :: reflection_pair ::
    rcons (rcons (phase_factors (b::tail)) reflection_pair) (phase_pair phi)).
by rewrite IH.
Qed.

Lemma phase_factors_rev phases : phase_factors (rev phases) = rev (phase_factors phases).
Proof.
elim: phases=> [|phi tail IH]; first by [].
rewrite rev_cons phase_factors_rcons.
case: tail IH=> [|a tail] IH; first by [].
change ((if rev (a :: tail) is [::] then [:: phase_pair phi]
  else rcons (rcons (phase_factors (rev (a :: tail))) reflection_pair) (phase_pair phi)) =
  rev (phase_pair phi :: reflection_pair :: phase_factors (a :: tail))).
rewrite [RHS]rev_cons [rev (reflection_pair :: _)]rev_cons IH.
have ne : rev (a :: tail) != [::] by rewrite -size_eq0 size_rev.
by case: (rev (a :: tail)) ne.
Qed.

Lemma phase_factors_neg phases :
  phase_factors (map -%R phases) = map pair_adjoint (phase_factors phases).
Proof.
elim: phases=> [|phi tail IH]; first by [].
case: tail IH=> [|a tail] IH.
- change ([:: phase_pair (-phi)] = [:: pair_adjoint (phase_pair phi)]).
  by rewrite pair_adjoint_phase.
- change (phase_pair (-phi) :: reflection_pair :: phase_factors (map -%R (a::tail)) =
    pair_adjoint (phase_pair phi) :: pair_adjoint reflection_pair ::
    map pair_adjoint (phase_factors (a::tail))).
  by rewrite pair_adjoint_phase pair_adjoint_reflection IH.
Qed.

Definition qsp_sequence (phases : seq R) := pair_fold (phase_factors phases).
Lemma phase_factors_cons_rcons phi tail last :
  phase_factors (rcons (phi :: tail) last) =
  phase_pair phi :: reflection_pair :: phase_factors (rcons tail last).
Proof. by case: tail. Qed.
Lemma qsp_sequence_rcons prefix last :
  qsp_sequence (rcons prefix last) = qsp_pair prefix last.
Proof.
elim: prefix=> [|phi tail IH].
- by rewrite /qsp_sequence /= /pair_fold /= pair_product1r.
- rewrite /qsp_sequence phase_factors_cons_rcons.
  change (pair_product (phase_pair phi)
    (pair_product reflection_pair (qsp_sequence (rcons tail last))) =
    qsp_step phi (qsp_pair tail last)).
  by rewrite IH qsp_step_product.
Qed.
Theorem qsp_sequence_adjoint phases :
  pair_adjoint (qsp_sequence phases) = qsp_sequence (map -%R (rev phases)).
Proof.
by rewrite /qsp_sequence pair_fold_adjoint phase_factors_neg phase_factors_rev.
Qed.

End Algebra.
End QSVTPairAlgebra.


Module QSVTTopCoefficient.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Import QSVTPolynomial.
Local Open Scope ring_scope.

Section Product.
Variable K : ringType.

Lemma coef_product_top (p q : {poly K}) m n :
  (forall i, (m < i)%N -> p`_i = 0) ->
  (forall i, (n < i)%N -> q`_i = 0) ->
  (p * q)`_(m + n) = p`_m * q`_n.
Proof.
move=> hp hq.
have hm : (m < (m + n).+1)%N by rewrite ltnS leq_addr.
pose j0 := Ordinal hm.
have hrest : \sum_(i < (m + n).+1 | i != j0)
    p`_i * q`_(m + n - i) = 0.
  apply: big1=> i.
  rewrite -val_eqE neq_ltn /= => /orP[him | hmi].
    have hn : (n < m + n - i)%N.
      by rewrite ltn_subRL ltn_add2r.
    by rewrite (hq _ hn) mulr0.
  by rewrite (hp _ hmi) mul0r.
by rewrite coefM (bigD1 j0) //= hrest /j0 /= addKn addr0.
Qed.

End Product.

Section LeadingCancellation.
Variable R : realType.
Local Notation C := R[i].
Local Notation poly := {poly C}.

Lemma valid_pair_top_coefficient k (p q : poly) :
  valid_pair k.+1 p q ->
  p`_k.+1 * (p`_k.+1)^*%C = q`_k * (q`_k)^*%C.
Proof.
move=> [hp hq hpp hqp hnorm].
have hpstar : degree_le (poly_star p) k.+1.
  by move=> i hi; rewrite poly_star_coef (hp _ hi) conjc0.
have hqle : degree_le q k.
  by move=> i hi; exact: hq i hi.
have hqstar : degree_le (poly_star q) k.
  by move=> i hi; rewrite poly_star_coef (hqle _ hi) conjc0.
have hqsize : (size (q * poly_star q)%R <= (k + k).+1)%N.
  apply/leq_sizeP=> i hi.
  rewrite coefM; apply: big1=> j _.
  case: (ltnP k j) => hkj.
    by rewrite (hqle _ hkj) mul0r.
  have hki : (k < i - j)%N.
    rewrite ltn_subRL.
    have hsum : (j + k <= k + k)%N by rewrite leq_add2r.
    exact: leq_ltn_trans hsum hi.
  by rewrite (hqstar _ hki) mulr0.
have hqtop : (q * poly_star q)`_(k.+1 + k.+1) = 0.
  apply: nth_default.
  apply: leq_trans hqsize _.
  by rewrite addSn addnS /= leqnSn.
have heq := congr1 (fun r : poly => r`_(k.+1 + k.+1)) hnorm.
have hguard : (k.+1 + k.+1 < 2)%N = false.
  by rewrite addSn addnS /=.
rewrite /norm_pair /defect coefD -mulrA mulrBl mul1r coefB
  coefXnM hguard hqtop in heq.
rewrite (coef_product_top hp hpstar) (poly_star_coef p) in heq.
have hindex : (k.+1 + k.+1 - 2)%N = (k + k)%N by rewrite addSn addnS !subSS subn0.
rewrite hindex (coef_product_top hqle hqstar) poly_star_coef coef1 /= in heq.
by move/eqP: heq; rewrite sub0r subr_eq0=> /eqP.
Qed.

End LeadingCancellation.
End QSVTTopCoefficient.

Module QSVTSynthesis.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex trigo.
Import QSVTPolynomial QSVTUnitCircle QSVTTopCoefficient.
Local Open Scope ring_scope.
Section Synthesis.
Variable R : realType.
Local Notation C := R[i].
Local Notation poly := {poly C}.

Lemma degree_lt_trim (p : poly) d :
  degree_lt p d.+2 -> p`_d = 0 -> p`_d.+1 = 0 -> degree_lt p d.
Proof.
move=> hp hd hd1 i hi.
have [->|id] := eqVneq i d; first exact: hd.
have di : (d < i)%N by rewrite ltn_neqAle eq_sym id hi.
have [->|id1] := eqVneq i d.+1; first exact: hd1.
have di1 : (d.+1 < i)%N by rewrite ltn_neqAle eq_sym id1 di.
exact: hp i di1.
Qed.

Lemma phase_cancel (p q : C) :
  p * p^*%C = q * q^*%C ->
  exists phi : R, (expi phi)^*%C * p = expi phi * q.
Proof.
move=> hpq.
have [q0|q0] := eqVneq q 0.
  have p0 : p = 0.
    move/eqP: hpq; rewrite q0 mul0r mulf_eq0 conjc_eq0 orbb=>/eqP.
    by [].
  by exists 0; rewrite p0 q0 !mulr0.
have qw : q * q^*%C != 0 by rewrite mulf_eq0 conjc_eq0 orbb.
have hw : (p / q) * (p / q)^*%C = 1.
  rewrite rmorph_div ?unitfE //.
  by rewrite mulrACA -invfM hpq divff.
have [phi hphi] := expi_double_surjective hw.
exists phi.
have hp : p = (expi phi * expi phi) * q.
  by rewrite -expiD hphi divfK.
rewrite hp !mulrA [(expi phi)^*%C * expi phi]mulrC expi_unit mul1r.
by [].
Qed.

Lemma qsp_peel_valid (phi : R) d p q :
  valid_pair d.+1 p q ->
  (expi phi)^*%C * p`_d.+1 = expi phi * q`_d ->
  valid_pair d (qsp_peel phi (p,q)).1 (qsp_peel phi (p,q)).2.
Proof.
move=> [hp hq hpp hqq hn] hc.
pose p0 := ((expi phi)^*%C)%:P * p.
pose q0 := (expi phi)%:P * q.
have epeel : qsp_peel phi (p,q) = ('X * p0 + (defect R) * q0, p0 - 'X * q0).
  by rewrite /qsp_peel /p0 /q0; cbn [fst snd]; congr (_, _); ring.
have hp0 : degree_lt p0 d.+2 by apply: degree_ltCM.
have hq0 : degree_lt q0 d.+1 by apply: degree_ltCM.
have pp0 : poly_parity p0 (~~ odd d).
  by apply: poly_parityCM; move: hpp; rewrite oddS.
have pq0 : poly_parity q0 (odd d).
  by apply: poly_parityCM; move: hqq; rewrite oddS negbK.
have ppar : poly_parity ('X * p0 + (defect R) * q0) (odd d).
  apply: poly_parityD; last exact: poly_parity_defectM pq0.
  by have := poly_parityXM pp0; rewrite negbK.
have qpar : poly_parity (p0 - 'X * q0) (~~ odd d).
  apply: poly_parityB pp0 _.
  exact: poly_parityXM pq0.
have pbound : degree_lt ('X * p0 + (defect R) * q0) d.+3.
  apply: degree_ltD; first exact: degree_ltXM hp0.
  exact: degree_lt_defectM hq0.
have qbound : degree_lt (p0 - 'X * q0) d.+2.
  apply: degree_ltB hp0 _.
  exact: degree_ltXM hq0.
have c0 : p0`_d.+1 = q0`_d by rewrite /p0 /q0 !coefCM.
have qlead : (p0 - 'X * q0)`_d.+1 = 0.
  by rewrite coefB coefXM /= c0 subrr.
have plead : ('X * p0 + (defect R) * q0)`_d.+2 = 0.
  have ed : (defect R) * q0 = q0 - 'X * ('X * q0).
    by rewrite /defect; ring.
  rewrite ed coefD coefB !coefXM /= c0.
  have hz : q0`_d.+2 = 0 := hq0 _ (leqnSn _).
  by rewrite hz; ring.
have pd : degree_le ('X * p0 + (defect R) * q0) d.
  apply: degree_lt_trim pbound _ plead.
  by apply: ppar; rewrite oddS; case: (odd d).
have qd : degree_lt (p0 - 'X * q0) d.
  apply: degree_lt_trim qbound _ qlead.
  by apply: qpar; case: (odd d).
rewrite epeel; constructor=> //.
have h := qsp_peel_norm phi p q.
by rewrite epeel in h; rewrite h.
Qed.

Lemma valid_pair0_phase p q : valid_pair 0 p q ->
  exists last : R, qsp_pair [::] last = (p,q).
Proof.
move=> [hp hq _ _ hn].
have pC : p = (p`_0)%:P := size1_polyC (proj1 (degree_le_size p 0) hp).
have q0 : q = 0 := proj1 (degree_lt0 q) hq.
have hu : p`_0 * (p`_0)^*%C = 1.
  apply: polyC_inj.
  by move: hn; rewrite /norm_pair {1 2}pC q0 poly_starC poly_star0
    !mulr0 addr0 -polyCM.
have [last he] := expi_surjective hu.
exists last; rewrite /qsp_pair he -pC q0.
by [].
Qed.

Theorem qsp_pair_converse d p q : valid_pair d p q ->
  exists (prefix : seq R) (last : R),
    (size prefix = d) /\ (qsp_pair prefix last = (p,q)).
Proof.
elim: d p q => [|d IH] p q hv.
- have [last he] := valid_pair0_phase hv.
  by exists [::], last.
- have [phi hc] := phase_cancel (valid_pair_top_coefficient hv).
  have hvp := qsp_peel_valid hv hc.
  have [prefix [last [hs he]]] := IH _ _ hvp.
  exists (phi :: prefix), last; split; first by rewrite /= hs.
  change (qsp_step phi (qsp_pair prefix last) = (p,q)).
  rewrite he.
  have ep : ((qsp_peel phi (p,q)).1, (qsp_peel phi (p,q)).2) =
    qsp_peel phi (p,q) by case: (qsp_peel phi (p,q)).
  by rewrite ep qsp_step_peel.
Qed.

Corollary valid_pair_synthesis_iff d p q :
  valid_pair d p q <->
  exists (prefix : seq R) (last : R),
    (size prefix = d) /\ (qsp_pair prefix last = (p,q)).
Proof.
split; first exact: qsp_pair_converse.
move=> [prefix [last [hs he]]].
have hv := qsp_pair_valid prefix last.
by rewrite hs he in hv.
Qed.

End Synthesis.
End QSVTSynthesis.

Module QSVTCompletionBudget.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Section Budget.
Variable F : realType.
Local Notation poly := {poly F}.
Definition real_parity (p : poly) (b : bool) := forall i, odd i != b -> p`_i=0.
Lemma real_parity0 b : real_parity 0 b.
Proof. by move=>i _; rewrite coef0. Qed.
Lemma real_parityC c : real_parity c%:P false.
Proof. by move=>[|i] //= _; rewrite coefC. Qed.
Lemma real_parityD p q b : real_parity p b -> real_parity q b -> real_parity (p+q) b.
Proof. by move=>hp hq i hi; rewrite coefD hp // hq // addr0. Qed.
Lemma real_parityB p q b : real_parity p b -> real_parity q b -> real_parity (p-q) b.
Proof. by move=>hp hq i hi; rewrite coefB hp // hq // subrr. Qed.
Lemma real_parityM p q b c : real_parity p b -> real_parity q c -> real_parity (p*q) (b (+) c).
Proof.
move=>hp hq i hi; rewrite coefM; apply: big1=>j _.
case Ej: (odd j == b).
- rewrite hq ?mulr0 //.
  move/eqP: Ej=>Ej.
  have Hj : (j<=i)%N by move: (ltn_ord j); rewrite ltnS.
  rewrite oddB // Ej.
  by move: hi; clear hp hq Ej; case: b; case: c; case: (odd i).
- by rewrite hp ?mul0r //; rewrite Ej.
Qed.
Definition completion_budget d (B C : poly) :=
  [ /\ (size B <= d.+1)%N, (size C <= d)%N,
       real_parity B (odd d) & real_parity C (~~odd d)].
Lemma size_mul_bound (p q : poly) m n :
  (size p<=m.+1)%N -> (size q<=n.+1)%N -> (size (p*q)%R<= (m+n).+1)%N.
Proof.
move=>hp hq; apply: leq_trans (size_polyMleq p q) _.
have h := leq_sub2r 1 (leq_add hp hq).
by rewrite !subn1 addSn addnS /= in h.
Qed.
Lemma size_mul_lt_bound (p q : poly) m n :
  (size p<=m.+1)%N -> (size q<=n)%N -> (size (p*q)%R<= m+n)%N.
Proof.
move=>hp hq; apply: leq_trans (size_polyMleq p q) _.
have h := leq_sub2r 1 (leq_add hp hq).
by rewrite !subn1 addSn /= in h.
Qed.
Lemma real_parityX : real_parity ('X:poly) true.
Proof. by move=>[|[|i]] //= hi; rewrite coefX. Qed.
Lemma real_parity_defect : real_parity (QSVTCompletion.completion_defect F) false.
Proof.
apply: real_parityB; first exact: real_parityC.
have h := real_parityM real_parityX real_parityX.
by rewrite -expr2 in h.
Qed.
Lemma size_sub_bound (p q : poly) n :
  (size p<=n)%N -> (size q<=n)%N -> (size (p-q)%R<=n)%N.
Proof.
by move=>hp hq; apply: leq_trans (size_polyD p (-q)) _;
  rewrite size_polyN geq_max hp hq.
Qed.
Lemma size_sum_bound (p q : poly) n :
  (size p<=n)%N -> (size q<=n)%N -> (size (p+q)%R<=n)%N.
Proof.
by move=>hp hq; apply: leq_trans (size_polyD p q) _; rewrite geq_max hp hq.
Qed.
Lemma completion_product_budget r s B C D E :
  completion_budget r B C -> completion_budget s D E ->
  completion_budget (r+s)
    (QSVTCompletion.completion_product (B,C) (D,E)).1
    (QSVTCompletion.completion_product (B,C) (D,E)).2.
Proof.
move=>[hB hC pB pC] [hD hE pD pE].
rewrite /QSVTCompletion.completion_product /=; constructor.
- apply: size_sub_bound; first exact: size_mul_bound hB hD.
  have hF : (size (QSVTCompletion.completion_defect F)<=3)%N.
    apply: size_sub_bound; by rewrite ?size_poly1 ?size_polyXn.
  have hFC := size_mul_lt_bound hF hC.
  have hFCE := size_mul_lt_bound hFC hE.
  by rewrite addSn in hFCE.
- apply: size_sum_bound.
  + exact: size_mul_lt_bound hB hE.
  + rewrite mulrC addnC; exact: size_mul_lt_bound hD hC.
- rewrite oddD; apply: real_parityB.
  + exact: real_parityM pB pD.
  + have h := real_parityM (real_parityM real_parity_defect pC) pE.
    move: h; clear pB pC pD pE; by case: (odd r); case: (odd s).
- rewrite oddD; apply: real_parityD.
  + have h := real_parityM pB pE.
    move: h; clear pB pC pD pE; by case: (odd r); case: (odd s).
  + have h := real_parityM pC pD.
    move: h; clear pB pC pD pE; by case: (odd r); case: (odd s).
Qed.
Lemma real_parityZ k p b : real_parity p b -> real_parity (k*:p) b.
Proof. by move=>hp i hi; rewrite coefZ hp // mulr0. Qed.
Lemma completion_budget_zero d : completion_budget d 0 0.
Proof. constructor; try by rewrite size_poly0.
all: exact: real_parity0.
Qed.
Lemma completion_budget_constant k : completion_budget 0 k%:P 0.
Proof. constructor; try by rewrite ?size_poly0 ?size_polyC.
- exact: size_polyC_leq1.
- exact: real_parityC.
- exact: real_parity0.
Qed.
Lemma completion_budget_padding : completion_budget 1 ('X:poly) 1.
Proof. constructor; try by rewrite ?size_polyX ?size_poly1.
- exact: real_parityX.
- exact: real_parityC.
Qed.
Lemma completion_budget_pad r B C : completion_budget r B C ->
  completion_budget r.+1 (QSVTCompletion.completion_pad_step (B,C)).1
    (QSVTCompletion.completion_pad_step (B,C)).2.
Proof.
move=>hp; have h := completion_product_budget hp completion_budget_padding.
by rewrite addn1 in h.
Qed.
Lemma completion_padding_budget n r B C : completion_budget r B C ->
  completion_budget (r+n) (QSVTCompletion.completion_padding n (B,C)).1
    (QSVTCompletion.completion_padding n (B,C)).2.
Proof.
elim: n r B C=>[|n IH] r B C hp; first by rewrite addn0.
change (completion_budget (r+n.+1)
  (QSVTCompletion.completion_pad_step (QSVTCompletion.completion_padding n (B,C))).1
  (QSVTCompletion.completion_pad_step (QSVTCompletion.completion_padding n (B,C))).2).
rewrite addnS [QSVTCompletion.completion_padding n (B,C)]surjective_pairing.
exact: completion_budget_pad (IH _ _ _ hp).
Qed.
Lemma completion_budget_linear (a b : F) :
  completion_budget 1 (a*:('X:poly)) b%:P.
Proof.
constructor.
- by apply: leq_trans (size_scale_leq _ _) _; rewrite size_polyX.
- exact: size_polyC_leq1.
- exact: real_parityZ real_parityX.
- exact: real_parityC.
Qed.
Lemma completion_budget_quadratic (a b c : F) :
  completion_budget 2 (a*:('X^2:poly)-b%:P) (c*:('X:poly)).
Proof.
constructor.
- apply: size_sub_bound.
  + by apply: leq_trans (size_scale_leq _ _) _; rewrite size_polyXn.
  + by apply: leq_trans (size_polyC_leq1 _) _.
- by apply: leq_trans (size_scale_leq _ _) _; rewrite size_polyX.
- apply: real_parityB; last exact: real_parityC.
  apply: real_parityZ.
  have h := real_parityM real_parityX real_parityX.
  by rewrite -expr2 in h.
- exact: real_parityZ real_parityX.
Qed.
Lemma coef_comp_neg (p : poly) i : (p \Po -'X)`_i = (-1)^+i * p`_i.
Proof.
elim/poly_ind: p=>[|p a IH] in i *.
- by rewrite comp_poly0 !coef0 mulr0.
- rewrite comp_polyD comp_polyM comp_polyX comp_polyC mulrN coefD coefN.
  case: i=>[|i]; rewrite !coefMX !coefC /= ?expr0 ?mul1r ?add0r ?oppr0 //.
  + by rewrite coefD coefMX coefC /= !add0r.
  + by rewrite coefD coefMX coefC /= !addr0 IH exprS mulN1r mulNr.
Qed.
Lemma real_parity_evenE (p : poly) : real_parity p false <-> p \Po -'X = p.
Proof.
split=>[hp|he].
- apply/polyP=>i; rewrite coef_comp_neg -signr_odd.
  case Ei: (odd i).
  + have hz : p`_i=0 by apply: hp; rewrite Ei.
    by rewrite hz mulr0.
  + by rewrite expr0 mul1r.
- move=>i hi; have h := congr1 (fun q:poly=>q`_i) he.
  rewrite coef_comp_neg -signr_odd in h.
  have Ei : odd i = true by move: hi; case: (odd i).
  rewrite Ei expr1 mulN1r in h.
  have h2 : p`_i *+ 2 = 0 by rewrite mulr2n -[X in X + _]h addNr.
  by move/eqP: h2; rewrite -mulr_natr mulf_eq0 pnatr_eq0 /= orbF=>/eqP.
Qed.
End Budget.
End QSVTCompletionBudget.

Module QSVTRootOrbits.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Local Open Scope ring_scope.

Section Orbits.
Variable R : realType.
Local Notation C := R[i].

Definition real_embed (p : {poly R}) := map_poly (real_complex R) p.

Lemma real_embed_star p : map_poly conjc (real_embed p) = real_embed p.
Proof.
apply/polyP=> i; rewrite /real_embed !coef_map.
exact: conjc_real.
Qed.

Lemma real_embed_even p : p \Po (-'X) = p ->
  (real_embed p) \Po (-'X) = real_embed p.
Proof.
move=> hp.
have he := congr1 real_embed hp.
rewrite /real_embed map_comp_poly rmorphN in he.
change (real_embed p \Po (- map_poly (real_complex R) ('X : {poly R})) = real_embed p) in he.
rewrite map_polyX in he.
exact: he.
Qed.

Lemma root_real_conj p z : root (real_embed p) z^*%C = root (real_embed p) z.
Proof. by rewrite -complex_root_conj real_embed_star. Qed.

Lemma root_even_neg (p : {poly C}) z : p \Po (-'X) = p ->
  root p (-z) = root p z.
Proof.
move=> hp.
have he := congr1 (fun q : {poly C} => q.[z]) hp.
rewrite horner_comp hornerN hornerX in he.
by rewrite /root he.
Qed.

Lemma eqrN (x : R) : (x == -x) = (x == 0).
Proof. by rewrite eq_sym eqNr. Qed.

Lemma quartet_uniq (a b : R) : a != 0 -> b != 0 ->
  uniq [:: (a +i* b)%C; -(a +i* b)%C;
            (a +i* b)%C^*%C; -((a +i* b)%C^*%C)].
Proof.
move=> ha hb.
simpc; rewrite /= !inE !eq_complex /= !eqNr !eqrN !eqxx.
by rewrite (negPf ha) (negPf hb).
Qed.

Lemma complex_constructorE (a b : R) :
  (a +i* b)%C = a%:C + 'i%C * b%:C.
Proof. by rewrite [LHS]complexE. Qed.

Lemma quartet_factor_product (a b : R) :
  \prod_(z <- [:: (a +i* b)%C; -(a +i* b)%C;
                 (a +i* b)%C^*%C; -((a +i* b)%C^*%C)]) ('X - z%:P) =
  real_embed ('X ^+ 4 + (2 * (b ^+ 2 - a ^+ 2))%:P * 'X ^+ 2 +
    ((a ^+ 2 + b ^+ 2) ^+ 2)%:P).
Proof.
rewrite !big_cons big_nil mulr1.
simpc.
have hconj : (a +i* b)%C^*%C = (a -i* b)%C by [].
rewrite hconj.
rewrite (complex_constructorE a b) (complex_constructorE (-a) (-b))
  (complex_constructorE a (-b)) (complex_constructorE (-a) b).
have hX : real_embed ('X : {poly R}) = ('X : {poly C}).
  exact: map_polyX.
have hI : (('i%C : C)%:P : {poly C}) ^+ 2 = -1.
  by rewrite -polyC_exp sqr_i polyCN polyC1.
rewrite /real_embed in hX *.
rewrite !rmorphD !rmorphM /= ?map_polyX ?map_polyC.
ring: hX hI.
Qed.

Lemma quartet_divides (p : {poly R}) (a b : R) :
  p \Po (-'X) = p -> a != 0 -> b != 0 ->
  root (real_embed p) (a +i* b)%C ->
  ('X ^+ 4 + (2 * (b ^+ 2 - a ^+ 2))%:P * 'X ^+ 2 +
    ((a ^+ 2 + b ^+ 2) ^+ 2)%:P) %| p.
Proof.
move=> heven ha hb hz.
have hceven := real_embed_even heven.
rewrite -(dvdp_map (real_complex R)).
rewrite -/(real_embed _) -quartet_factor_product.
apply: uniq_roots_dvdp; last by rewrite uniq_rootsE; exact: quartet_uniq.
rewrite /= !root_even_neg //.
have hzc : root (real_embed p) (a -i* b)%C.
  change (is_true (root (real_embed p) (a +i* b)%C^*%C)).
  by rewrite root_real_conj hz.
by rewrite -/(real_embed p) hz hzc.
Qed.

Lemma imaginary_pair_uniq (b : R) : b != 0 ->
  uniq [:: (0 +i* b)%C; -(0 +i* b)%C].
Proof.
move=> hb; simpc; rewrite /= !inE !eq_complex /= !eqxx ?eqNr ?eqrN.
by rewrite (negPf hb).
Qed.

Lemma imaginary_factor_product (b : R) :
  \prod_(z <- [:: (0 +i* b)%C; -(0 +i* b)%C]) ('X - z%:P) =
  real_embed ('X ^+ 2 + (b ^+ 2)%:P).
Proof.
rewrite !big_cons big_nil mulr1; simpc.
rewrite (complex_constructorE 0 b) (complex_constructorE 0 (-b)).
have hX : real_embed ('X : {poly R}) = ('X : {poly C}).
  exact: map_polyX.
have hI : (('i%C : C)%:P : {poly C}) ^+ 2 = -1.
  by rewrite -polyC_exp sqr_i polyCN polyC1.
rewrite /real_embed in hX *.
rewrite !rmorphD !rmorphM /= ?map_polyX ?map_polyC.
ring: hX hI.
Qed.

Lemma imaginary_divides (p : {poly R}) (b : R) :
  p \Po (-'X) = p -> b != 0 -> root (real_embed p) (0 +i* b)%C ->
  ('X ^+ 2 + (b ^+ 2)%:P) %| p.
Proof.
move=> heven hb hz.
have hceven := real_embed_even heven.
rewrite -(dvdp_map (real_complex R)).
rewrite -/(real_embed _) -imaginary_factor_product.
apply: uniq_roots_dvdp; last by rewrite uniq_rootsE; exact: imaginary_pair_uniq.
by rewrite /= !root_even_neg // -/(real_embed p) hz.
Qed.

End Orbits.
End QSVTRootOrbits.

Module QSVTRealDivisors.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Import QSVTRootEven.
Local Open Scope ring_scope.
Section Divisors.
Variable R : realType.
Local Notation poly := {poly R}.

Lemma even_rootN (p : poly) a : p \Po (-'X) = p -> root p (-a) = root p a.
Proof.
move=> he; have h := congr1 (fun q : poly => q.[a]) he.
rewrite horner_comp hornerN hornerX in h.
by rewrite /root h.
Qed.

Lemma even_positive_mup_ge2 (p : poly) a : p != 0 -> root p a ->
  ~~ odd (mup a p) -> (2 <= mup a p)%N.
Proof.
move=> hp hr hm.
have hm0 : (0 < mup a p)%N by rewrite -XsubC_dvd // -root_factor_theorem.
by move: hm0 hm; case: (mup a p)=> [|[|n]].
Qed.

Lemma zero_root_divides (p : poly) : p != 0 ->
  (forall x, -1 <= x <= 1 -> 0 <= p.[x]) -> root p 0 -> ('X^2 %| p).
Proof.
move=> hp hn hr.
have hinterval : (-1 < (0:R) < 1) by rewrite ltrN10 ltr01.
have hm := even_positive_mup_ge2 hp hr (interior_root_even hp hinterval hn).
by move: hm; rewrite mup_geq // subr0.
Qed.

Lemma real_pair_coprime (a : R) : a != 0 ->
  coprimep ('X - a%:P : poly) ('X - (-a)%:P).
Proof.
move=> ha; apply: coprimep_XsubC2.
by rewrite -opprD oppr_eq0 -mulr2n -mulr_natr mulf_eq0 pnatr_eq0 /= orbF.
Qed.

Lemma real_pair_factor (a : R) :
  ('X - a%:P) * ('X - (-a)%:P) = 'X^2 - (a^+2)%:P :> poly.
Proof. rewrite polyCN polyC_exp; ring. Qed.

Lemma real_pair_divides (p : poly) a :
  p \Po (-'X) = p -> a != 0 -> root p a ->
  ((a^+2)%:P - 'X^2) %| p.
Proof.
move=> he ha hr.
have hrN : root p (-a) by rewrite even_rootN.
have hm : (('X-a%:P) * ('X-(-a)%:P) %| p).
  by rewrite Gauss_dvdp ?real_pair_coprime // -!root_factor_theorem hr hrN.
by move: hm; rewrite real_pair_factor -opprB dvdpNl.
Qed.

Lemma real_interior_divides (p : poly) a :
  p != 0 -> p \Po (-'X) = p -> a != 0 -> -1 < a < 1 ->
  (forall x, -1 <= x <= 1 -> 0 <= p.[x]) -> root p a ->
  (('X^2 - (a^+2)%:P)^+2 %| p).
Proof.
move=> hp he ha hai hn hr.
have hrN : root p (-a) by rewrite even_rootN.
have haiN : -1 < -a < 1.
  have /andP[hl hu] := hai.
  by apply/andP; split; [rewrite ltrNr opprK | rewrite ltrNl].
have hma := even_positive_mup_ge2 hp hr (interior_root_even hp hai hn).
have hmaN := even_positive_mup_ge2 hp hrN (interior_root_even hp haiN hn).
have hcop := coprimep_expl 2 (coprimep_expr 2 (real_pair_coprime ha)).
have hm : (('X-a%:P)^+2 * ('X-(-a)%:P)^+2 %| p).
  by rewrite Gauss_dvdp // -!mup_geq // hma hmaN.
have hef : ('X-a%:P)^+2 * ('X-(-a)%:P)^+2 =
  ('X^2-(a^+2)%:P)^+2.
  by rewrite -exprMn real_pair_factor.
by rewrite -hef.
Qed.

End Divisors.
End QSVTRealDivisors.

Module QSVTRootClassification.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Import QSVTRootOrbits QSVTRealDivisors.
Local Open Scope ring_scope.
Section Classification.
Variable R : realType.
Local Notation poly := {poly R}.

Inductive root_factor_cases (p : poly) : Prop :=
| FactorZero : ('X^2 %| p) -> root_factor_cases p
| FactorInterior : forall a : R, a != 0 -> -1 < a < 1 ->
    (('X^2-(a^+2)%:P)^+2 %| p) -> root_factor_cases p
| FactorOutside : forall a : R, 1 <= a^+2 ->
    (((a^+2)%:P-'X^2) %| p) -> root_factor_cases p
| FactorImaginary : forall b : R, b != 0 ->
    (('X^2+(b^+2)%:P) %| p) -> root_factor_cases p
| FactorQuartet : forall a b : R, a != 0 -> b != 0 ->
    (('X^4 + (2*(b^+2-a^+2))%:P * 'X^2 +
             ((a^+2+b^+2)^+2)%:P) %| p) -> root_factor_cases p.

Lemma root_factor_classification (p : poly) :
  p != 0 -> (1 < size p)%N -> p \Po (-'X) = p ->
  (forall x, -1 <= x <= 1 -> 0 <= p.[x]) -> root_factor_cases p.
Proof.
move=> hp hs he hn.
have [z hz] : exists z, root (real_embed p) z.
  apply/closed_rootP.
  by rewrite /real_embed size_map_poly (gtn_eqF hs).
case: z hz=> a b hz.
have [b0|b0] := eqVneq b 0.
- subst b.
  have hr : root p a.
    move: hz; rewrite /root /real_embed horner_map.
    move/eqP=> hz; apply/eqP.
    have hh := congr1 (@Re R) hz.
    by move: hh; rewrite /=.
  have [a0|a0] := eqVneq a 0.
  + subst a; apply: FactorZero; exact: zero_root_divides hp hn hr.
  + have [hai|hao] := ltrP (a^+2) 1.
    * have hain : -1 < a < 1.
        rewrite -ltr_norml.
        have hna : `|a|^+2 < 1 by rewrite real_normK ?num_real.
        by move: hna; rewrite expr_lt1 ?normr_ge0.
      exact: FactorInterior a0 hain (real_interior_divides hp he a0 hain hn hr).
    * exact: FactorOutside hao (real_pair_divides he a0 hr).
- have [a0|a0] := eqVneq a 0.
  + subst a; exact: FactorImaginary b0 (imaginary_divides he b0 hz).
  + exact: FactorQuartet a0 b0 (quartet_divides he a0 b0 hz).
Qed.

End Classification.
End QSVTRootClassification.

Module QSVTRealCompletion.
Import Order.TTheory GRing.Theory Num.Def Num.Theory QSVTCompletionBudget.
Local Open Scope ring_scope.
Section Assembly.
Variable F : realType.
Local Notation poly := {poly F}.
Definition interval_nonnegative (p : poly) := forall x:F, -1<=x<=1 -> 0<=p.[x].
Lemma interval_square_bound (x:F) : -1<=x<=1 -> x^+2<=1.
Proof.
move=>hx; have hax : `|x|<=1 by rewrite ler_norml.
have hs : `|x|^+2<=1 by rewrite expr_le1 ?normr_ge0.
by rewrite -normrX ger0_norm ?sqr_ge0 in hs.
Qed.
Lemma completion_norm_nonnegative (B C : poly) :
  interval_nonnegative (QSVTCompletion.completion_norm B C).
Proof.
move=>x hx; rewrite /QSVTCompletion.completion_norm /QSVTCompletion.completion_defect
  !(hornerD,hornerN,horner_exp,hornerM,hornerC,hornerX).
apply: addr_ge0; first exact: sqr_ge0.
apply: mulr_ge0; last exact: sqr_ge0.
by rewrite subr_ge0; exact: interval_square_bound hx.
Qed.
Lemma completion_small_constant (p:poly) : (size p<=1)%N ->
  interval_nonnegative p -> exists B C, completion_budget 0 B C /\
    QSVTCompletion.completion_norm B C=p.
Proof.
move=>hs hp.
have Ep : p = (p`_0)%:P.
  apply/polyP=>i; case: i=>[|i]; rewrite coefC /=; first by [].
  by rewrite nth_default // (leq_trans hs).
have hc : 0<=p`_0.
  have h := hp 0; rewrite Ep hornerC in h.
  by apply: h; rewrite lerN10 ler01.
exists (Num.sqrt p`_0)%:P,0; split; first exact: completion_budget_constant.
by rewrite QSVTCompletion.completion_norm_constant sqr_sqrtr // -Ep.
Qed.
Definition factor_witness r (f:poly) := exists B C,
  completion_budget r B C /\ QSVTCompletion.completion_norm B C=f.
Lemma factor_zero : factor_witness 1 ('X^2:poly).
Proof.
exists 'X,0; split.
- have h := completion_budget_linear (1:F) (0:F).
  by rewrite scale1r polyC0 in h.
- by rewrite /QSVTCompletion.completion_norm expr0n // mulr0 addr0.
Qed.
Lemma factor_inside (a:F) : factor_witness 2 (('X^2-(a^+2)%:P)^+2).
Proof.
exists ('X^2-(a^+2)%:P),0; split.
- have h := completion_budget_quadratic (1:F) (a^+2) (0:F).
  by rewrite scale1r scale0r in h.
- by rewrite /QSVTCompletion.completion_norm expr0n // mulr0 addr0.
Qed.
Lemma factor_outside (a:F) : 1<=a^+2 -> factor_witness 1 ((a^+2)%:P-'X^2).
Proof.
move=>ha; exists ((Num.sqrt (a^+2-1))*:('X:poly)),a%:P; split.
- exact: completion_budget_linear.
- rewrite -mul_polyC /QSVTCompletion.completion_norm /QSVTCompletion.completion_defect
    !exprMn -!polyC_exp sqr_sqrtr ?subr_ge0 //.
  ring.
Qed.
Lemma factor_imaginary (b:F) : factor_witness 1 ('X^2+(b^+2)%:P).
Proof.
exists ((Num.sqrt (1+b^+2))*:('X:poly)),b%:P; split.
- exact: completion_budget_linear.
- rewrite -mul_polyC; exact: QSVTCompletion.completion_imaginary_factor.
Qed.
Lemma completion_norm_even d (B C:poly) : completion_budget d B C ->
  QSVTCompletion.completion_norm B C \Po -'X = QSVTCompletion.completion_norm B C.
Proof.
move=>[_ _ hb hc]; apply/real_parity_evenE.
apply: real_parityD.
- rewrite expr2; have h := real_parityM hb hb.
  by case: (odd d) hb hc h=> //.
- rewrite expr2; have h := real_parityM hc hc.
  have hc2 : real_parity (C*C) false by move: h; clear hb hc; case: (odd d).
  exact: real_parityM (real_parity_defect F) hc2.
Qed.
Lemma factor_quartet (a b:F) : factor_witness 2
  ('X^4+(2*(b^+2-a^+2))%:P*'X^2+((a^+2+b^+2)^+2)%:P).
Proof.
exists ((QSVTCompletion.completion_gamma a b)*:('X^2:poly)-(a^+2+b^+2)%:P),
  ((Num.sqrt ((QSVTCompletion.completion_gamma a b)^+2-1))*:('X:poly)); split.
- exact: completion_budget_quadratic.
- rewrite -!mul_polyC; exact: QSVTCompletion.completion_quartet_factor.
Qed.
Lemma size_inside_factor (a:F) : size (('X^2-(a^+2)%:P)^+2:poly)=5%N.
Proof.
have h : ('X^2-(a^+2)%:P:poly)!=0.
  by rewrite -size_poly_eq0 size_XnsubC.
by rewrite expr2 size_mul // size_XnsubC.
Qed.
Lemma size_outside_factor (a:F) : size ((a^+2)%:P-'X^2:poly)=3%N.
Proof. by rewrite -opprB size_polyN size_XnsubC. Qed.
Lemma size_quartet_factor (a b:F) :
  size ('X^4+(2*(b^+2-a^+2))%:P*'X^2+((a^+2+b^+2)^+2)%:P:poly)=5%N.
Proof.
rewrite -addrA size_polyDl ?size_polyXn //.
apply: size_sum_bound.
- rewrite mul_polyC; by apply: leq_trans (size_scale_leq _ _) _; rewrite size_polyXn.
- by apply: leq_trans (size_polyC_leq1 _) _.
Qed.

Lemma factor_decomposition (p:poly) : p!=0 -> (1<size p)%N ->
  p \Po -'X=p -> interval_nonnegative p ->
  exists (r:nat) (f B C:poly), [ /\ (0<r)%N, size f=(2*r).+1,
    completion_budget r B C, QSVTCompletion.completion_norm B C=f & f %| p].
Proof.
move=>hp hs he hn.
have pack r (f:poly) : (0<r)%N -> size f=(2*r).+1 ->
    factor_witness r f -> f %| p ->
    exists (r:nat) (f B C:poly), [ /\ (0<r)%N, size f=(2*r).+1,
      completion_budget r B C, QSVTCompletion.completion_norm B C=f & f %| p].
  move=>hr hf [B [C [hb hc]]] hd.
  by exists r,f,B,C; constructor.
case: (QSVTRootClassification.root_factor_classification hp hs he hn)=>
  [hd|a ha hi hd|a ha hd|b hb hd|a b ha hb hd].
- apply: (pack 1 ('X^2)); first by [].
  + by rewrite size_polyXn.
  + exact: factor_zero.
  + exact: hd.
- apply: (pack 2 (('X^2-(a^+2)%:P)^+2)); first by [].
  + by rewrite size_inside_factor.
  + exact: factor_inside.
  + exact: hd.
- apply: (pack 1 ((a^+2)%:P-'X^2)); first by [].
  + by rewrite size_outside_factor.
  + exact: factor_outside ha.
  + exact: hd.
- apply: (pack 1 ('X^2+(b^+2)%:P)); first by [].
  + by rewrite size_XnaddC.
  + exact: factor_imaginary.
  + exact: hd.
- apply: (pack 2 ('X^4+(2*(b^+2-a^+2))%:P*'X^2+((a^+2+b^+2)^+2)%:P)); first by [].
  + by rewrite size_quartet_factor.
  + exact: factor_quartet.
  + exact: hd.
Qed.

Theorem even_nonnegative_completion d (p:poly) :
  (size p <= (2*d).+1)%N -> p \Po -'X=p -> interval_nonnegative p ->
  exists B C, completion_budget d B C /\ QSVTCompletion.completion_norm B C=p.
Proof.
elim/ltn_ind: d p=>d IH p hs he hn.
have [hsmall|hbig] := leqP (size p) 1.
- have [B [C [hb hc]]] := completion_small_constant hsmall hn.
  exists (QSVTCompletion.completion_padding d (B,C)).1,
    (QSVTCompletion.completion_padding d (B,C)).2; split.
  + have h := completion_padding_budget d hb.
    by rewrite add0n in h.
  + by rewrite QSVTCompletion.completion_padding_norm hc.
- have hp : p!=0.
    apply/negP=>/eqP Hp; by rewrite Hp size_poly0 in hbig.
  have [r [f [B [C [hr hf hb hnf hd]]]]] := factor_decomposition hp hbig he hn.
  have hfnz : f!=0 by rewrite -size_poly_eq0 hf.
  pose q := p %/ f.
  have Ep : p=f*q by rewrite /q mulrC divpK.
  have hq : q!=0.
    apply/negP=>/eqP hq0; by move: hp; rewrite Ep hq0 mulr0 eqxx.
  have hfe : f \Po -'X=f by rewrite -hnf; exact: completion_norm_even hb.
  have hqe : q \Po -'X=q.
    exact: QSVTCompletionReduction.even_divisor_quotient hfnz hfe he hd.
  have hqn : interval_nonnegative q.
    apply: QSVTRootEven.nonnegative_factor_quotient hfnz _ _.
    + by rewrite -hnf; exact: completion_norm_nonnegative.
    + move=>x hx; rewrite -hornerM -Ep; exact: hn x hx.
  have Hsize : size p=(2*r+size q)%N by rewrite Ep size_mul // hf addSn.
  have Hqpos : (0<size q)%N by rewrite lt0n size_poly_eq0.
  have Hlower : ((2*r).+1<=size p)%N by rewrite Hsize -addn1 leq_add2l.
  have Hrd : (r<=d)%N.
    by move: (leq_trans Hlower hs); rewrite ltnS leq_mul2l.
  have Hrsub : (d-r<d)%N by rewrite ltn_subrL hr (leq_trans hr Hrd).
  have Hdouble : (2*r<=2*d)%N by rewrite leq_mul2l /= Hrd.
  have Hqs : (size q <= (2*(d-r)).+1)%N.
    by rewrite mulnBr -subSn // leq_subRL ?(leq_trans Hdouble (leqnSn _)) // -Hsize.
  have [D [E [hde hne]]] := IH (d-r)%N Hrsub q Hqs hqe hqn.
  exists (QSVTCompletion.completion_product (B,C) (D,E)).1,
    (QSVTCompletion.completion_product (B,C) (D,E)).2; split.
  + have h := completion_product_budget hb hde.
    by rewrite subnKC in h.
  + by rewrite QSVTCompletion.completion_product_norm hnf hne -Ep.
Qed.
End Assembly.
End QSVTRealCompletion.

Module QSVTRealPair.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex.
Import QSVTPolynomial QSVTCompletion QSVTCompletionBudget QSVTSynthesis.
Local Open Scope ring_scope.

Section Completion.
Variable R : realType.
Local Notation C := R[i].
Local Notation rpoly := {poly R}.
Local Notation cpoly := {poly C}.

Lemma abs_square_le1 (x : R) : `|x| <= 1 -> x ^+ 2 <= 1.
Proof.
move=>hx; have hsq := lerXn2r 2 (normr_ge0 x) (@ler01 R) hx.
by move: hsq; rewrite -normrX (ger0_norm (sqr_ge0 x)) expr1n.
Qed.

Definition r_embed (p : rpoly) := map_poly (real_complex R) p.
Definition complex_completion (p B : rpoly) :=
  r_embed p + ('i%C)%:P * r_embed B.

Lemma r_embed_star p : poly_star (r_embed p) = r_embed p.
Proof.
apply/polyP=>i; rewrite poly_star_coef /r_embed !coef_map.
exact: conjc_real.
Qed.

Lemma complex_completion_size (p B : rpoly) n :
  (size p <= n)%N -> (size B <= n)%N ->
  (size (complex_completion p B) <= n)%N.
Proof.
move=>hp hB; apply/leq_sizeP=>i hi.
rewrite /complex_completion coefD coefCM /r_embed !coef_map.
have hp0 : p`_i=0 by move/leq_sizeP: hp=>hpp; exact: (hpp i hi).
have hB0 : B`_i=0 by move/leq_sizeP: hB=>hBB; exact: (hBB i hi).
by rewrite hp0 hB0 !raddf0 mulr0 addr0.
Qed.

Lemma complex_completion_parity p B b :
  real_parity p b -> real_parity B b ->
  poly_parity (complex_completion p B) b.
Proof.
move=>hp hB i hi.
rewrite /complex_completion coefD coefCM /r_embed !coef_map hp // hB //.
by rewrite !raddf0 mulr0 addr0.
Qed.

Lemma complex_completion_real p B i :
  Re (complex_completion p B)`_i = p`_i.
Proof.
rewrite /complex_completion coefD coefCM /r_embed !coef_map.
change (Re ((p`_i)%:C + 'i%C * (B`_i)%:C) = p`_i).
by rewrite /=; ring.
Qed.

Lemma complex_completion_star_sum (p B : rpoly) :
  complex_completion p B + poly_star (complex_completion p B) = 2 *: r_embed p.
Proof.
have hi : ('i%C : C)^*%C = -'i%C by exact: conjCi.
rewrite /complex_completion poly_starD poly_starM !r_embed_star
  poly_starC hi polyCN -mul_polyC.
ring.
Qed.

Lemma imaginary_completion_star_sum (B : rpoly) :
  ('i%C)%:P * r_embed B + poly_star (('i%C)%:P * r_embed B) = 0.
Proof.
have hi : ('i%C : C)^*%C = -'i%C by exact: conjCi.
rewrite poly_starM r_embed_star poly_starC hi polyCN.
ring.
Qed.

Lemma real_pair_norm p q B D :
  norm_pair (complex_completion p B) (complex_completion q D) =
  r_embed (completion_norm p q + completion_norm B D).
Proof.
have hI : (('i%C : C)%:P : cpoly)^+2 = -1.
  by rewrite -polyC_exp sqr_i polyCN polyC1.
have hi : ('i%C : C)^*%C = -'i%C by exact: conjCi.
rewrite /norm_pair /complex_completion !poly_starD !poly_starM
  !r_embed_star poly_starC hi polyCN.
rewrite /r_embed /completion_norm /completion_defect /defect.
rewrite !rmorphD !rmorphM /= ?map_polyX ?map_polyC.
rewrite !rmorphB /= ?map_polyXn.
ring: hI.
Qed.

Lemma real_pair_valid d p q B D :
  completion_budget d p q -> completion_budget d B D ->
  completion_norm B D = 1 - completion_norm p q ->
  valid_pair d (complex_completion p B) (complex_completion q D).
Proof.
move=>[hp hq pp pq] [hB hD pB pD] hn.
constructor.
- apply/degree_le_size; exact: complex_completion_size hp hB.
- apply/degree_lt_size; exact: complex_completion_size hq hD.
- exact: complex_completion_parity pp pB.
- exact: complex_completion_parity pq pD.
- rewrite real_pair_norm hn addrC subrK /r_embed.
  exact: rmorph1.
Qed.

Definition residual (p q : rpoly) := 1 - completion_norm p q.

Lemma residual_size d p q : completion_budget d p q ->
  (size (residual p q) <= (2*d).+1)%N.
Proof.
move=>[hp hq pp pq].
have hpp := size_mul_bound hp hp.
have hdef : (size (completion_defect R) <= 3)%N.
  apply: size_sub_bound; by rewrite ?size_poly1 ?size_polyXn.
have hdq := size_mul_lt_bound hdef hq.
have hdqq := size_mul_lt_bound hdq hq.
rewrite addSn in hdqq.
have hnorm : completion_norm p q = p * p + (completion_defect R * q) * q by
  rewrite /completion_norm; ring.
have hsum := size_sum_bound hpp hdqq.
rewrite -hnorm in hsum.
have h1 : (size (1%R:rpoly) <= (d+d).+1)%N by rewrite size_poly1.
have hresult := size_sub_bound h1 hsum.
by rewrite /residual mul2n -addnn.
Qed.

Lemma residual_even d p q : completion_budget d p q ->
  (residual p q) \Po (-'X) = residual p q.
Proof.
move=>[hp hq pp pq]; apply/real_parity_evenE.
apply: real_parityB; first exact: real_parityC.
have ppp := real_parityM pp pp.
have pqq := real_parityM pq pq.
rewrite addbb in ppp pqq.
rewrite /completion_norm !expr2.
apply: real_parityD ppp _.
have pqq0 : real_parity (q * q) false by move: pqq; rewrite addbb.
have h := real_parityM (real_parity_defect R) pqq0.
exact: h.
Qed.

Lemma residual_nonnegative p q :
  (forall x, -1 <= x <= 1 -> (completion_norm p q).[x] <= 1) ->
  forall x, -1 <= x <= 1 -> 0 <= (residual p q).[x].
Proof.
move=>hb x hx; rewrite /residual !hornerE subr_ge0.
by move: (hb x hx); rewrite /completion_norm /completion_defect !hornerE.
Qed.

End Completion.

Section SynthesisTheorem.
Variable R : realType.
Let complete_even := @QSVTRealCompletion.even_nonnegative_completion R.

Theorem bounded_real_pair_completion d (p q : {poly R}) :
  completion_budget d p q ->
  (forall x, -1 <= x <= 1 -> (completion_norm p q).[x] <= 1) ->
  exists B D,
    completion_budget d B D /\
    completion_norm B D = residual p q /\
    valid_pair d (complex_completion p B) (complex_completion q D).
Proof.
move=>hbudget hbound.
have [B [D [hBD hnorm]]] := complete_even
  (residual_size hbudget) (residual_even hbudget) (residual_nonnegative hbound).
exists B,D; split=>//; split=>//.
exact: real_pair_valid hbudget hBD hnorm.
Qed.

Theorem bounded_real_pair_synthesis d (p q : {poly R}) :
  completion_budget d p q ->
  (forall x, -1 <= x <= 1 -> (completion_norm p q).[x] <= 1) ->
  exists B D (prefix : seq R) (last : R),
    completion_budget d B D /\
    completion_norm B D = residual p q /\
    size prefix = d /\
    qsp_pair prefix last = (complex_completion p B, complex_completion q D).
Proof.
move=>hbudget hbound.
have [B [D [hBD [hnorm hvalid]]]] := bounded_real_pair_completion hbudget hbound.
have [prefix [last [hlen hpair]]] := qsp_pair_converse hvalid.
by exists B,D,prefix,last.
Qed.

Definition admissible d (p : {poly R}) :=
  (size p <= d.+1)%N /\ real_parity p (odd d) /\
  (forall x, -1 <= x <= 1 -> `|p.[x]| <= 1).

Theorem real_qsp_full_witness d (p : {poly R}) : admissible d p ->
  exists B D (prefix : seq R) (last : R),
    completion_budget d B D /\
    completion_norm B D = residual p 0 /\
    size prefix = d /\
    qsp_pair prefix last =
      (complex_completion p B, ('i%C)%:P * r_embed D).
Proof.
move=>[hsize [hpar hbound]].
have hbudget : completion_budget d p 0.
  constructor=>//; first by rewrite size_poly0.
  exact: real_parity0.
have hb : forall x, -1 <= x <= 1 -> (completion_norm p 0).[x] <= 1.
  move=>x hx; rewrite /completion_norm !hornerE.
  by rewrite /= !mulr0 addr0; exact: abs_square_le1 (hbound x hx).
have [B [D [prefix [last [hBD [hnorm [hlen hpair]]]]]]] :=
  bounded_real_pair_synthesis hbudget hb.
exists B,D,prefix,last; split=>//; split=>//; split=>//.
by rewrite hpair /complex_completion /r_embed rmorph0 add0r.
Qed.

Theorem real_qsp_phase_witness d (p : {poly R}) : admissible d p ->
  exists (prefix : seq R) (last : R),
    size prefix = d /\
    (qsp_pair prefix last).1 + poly_star (qsp_pair prefix last).1 =
      2 *: r_embed p /\
    (qsp_pair prefix last).2 + poly_star (qsp_pair prefix last).2 = 0.
Proof.
move=>ha.
have [B [D [prefix [last [hBD [hnorm [hlen hpair]]]]]]] :=
  real_qsp_full_witness ha.
exists prefix,last; split=>//.
rewrite hpair /=; split.
- exact: complex_completion_star_sum.
- exact: imaginary_completion_star_sum.
Qed.

End SynthesisTheorem.
End QSVTRealPair.

(* Exact source convention bridge and symbolic acceptance examples, EN-F.1–2.
   The two-by-two identity retains its scalar factor.  All parameters x,s in
   that identity may be complex, so it includes s = sqrt(1-x^2). *)
Module QSVTExamples.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex trigo QSVTPolynomial.
Local Open Scope ring_scope.
Section Examples.
Variable R : realType.
Local Notation C := R[i].
Local Notation poly := {poly C}.

Lemma expi_pi_half : expi (pi / 2 : R) = 'i%C.
Proof. by rewrite /expi cos_pihalf sin_pihalf. Qed.
Lemma quarter_double : (pi / 4 + pi / 4 = pi / 2 :> R).
Proof.
rewrite -mulrDr -mulr2n -mulr_natr.
have h4 : (4 : R) = 2 * 2 by ring.
by rewrite h4 invfM -mulrA mulVf ?mulr1 // pnatr_eq0.
Qed.
Lemma half_double (a:R) : a/2+a/2=a.
Proof. by rewrite -mulrDr -mulr2n -mulr_natr mulVf ?mulr1 // pnatr_eq0. Qed.

Definition scalar_diagonal (theta : R) : 'M[C]_2 :=
  \matrix_(i,j) if i == j then if i == ord0 then expi theta else expi (-theta) else 0.
Definition scalar_reflection (x s : C) : 'M[C]_2 :=
  \matrix_(i,j) if i == j then if i == ord0 then x else -x else s.
Definition scalar_W (x s : C) : 'M[C]_2 :=
  \matrix_(i,j) if i == j then x else 'i%C * s.
Lemma expi_quarter_square : expi (pi / 4 : R) * expi (pi / 4) = 'i%C.
Proof. by rewrite -expiD quarter_double expi_pi_half. Qed.
Lemma expi_neg_quarter_square : expi (-(pi / 4) : R) * expi (-(pi / 4)) = -'i%C.
Proof.
rewrite -expiD -opprD quarter_double /expi cosN sinN cos_pihalf sin_pihalf.
by simpc.
Qed.

Theorem qsp_reflection_W_bridge (x s : C) :
  scalar_reflection x s =
  (-'i%C) *: (scalar_diagonal (pi/4) *m scalar_W x s *m scalar_diagonal (pi/4)).
Proof.
apply/matrixP; move=>i j.
case: i => [[|[|i]] Hi] //=.
all: case: j => [[|[|j]] Hj] //=.
all: rewrite /scalar_reflection /scalar_diagonal /scalar_W !mxE.
all: rewrite !big_ord_recr /= !big_ord0 !mxE /= !big_ord_recr /= !big_ord0 !mxE /=.
all: rewrite !mul0r !mulr0 !addr0 !add0r.
- rewrite [expi _ * x]mulrC -mulrA expi_quarter_square.
  by rewrite [x * 'i%C]mulrC mulrA mulNr -expr2 sqrCi opprK mul1r.
- rewrite [expi _ * ('i%C * s)]mulrC -mulrA -expiD addrN expi0 mulr1.
  by rewrite mulrA mulNr -expr2 sqrCi opprK mul1r.
- rewrite [expi _ * ('i%C * s)]mulrC -mulrA -expiD addNr expi0 mulr1.
  by rewrite mulrA mulNr -expr2 sqrCi opprK mul1r.
- rewrite [expi _ * x]mulrC -mulrA expi_neg_quarter_square.
  rewrite [x * -'i%C]mulrC mulrA mulrNN.
  by rewrite -expr2 sqrCi mulN1r.
Qed.

Lemma qsp_one_phase (a b : R) :
  qsp_pair [:: a] b =
  ((expi (a+b))%:P * 'X, (expi (b-a))%:P : poly).
Proof.
rewrite /qsp_pair /qsp_step /= !mulr0 addr0 subr0.
change (((expi a)%:P * ('X * (expi b)%:P), ((expi a)^*%C)%:P * (expi b)%:P) =
  ((expi (a+b))%:P * 'X, (expi (b-a))%:P : poly)).
by rewrite ['X * _]mulrC mulrA -!polyCM expi_conj -!expiD [(-a)+b]addrC.
Qed.

Lemma qsp_symmetric_two_phase (a b : R) :
  qsp_pair [:: a; b] a =
  ((expi (a+a+b))%:P * 'X^2 + (expi (a+a-b))%:P * defect R,
    (expi b - expi (-b))%:P * 'X : poly).
Proof.
change (qsp_step a (qsp_pair [:: b] a) =
  ((expi (a+a+b))%:P * 'X^2 + (expi (a+a-b))%:P * defect R,
    (expi b - expi (-b))%:P * 'X : poly)).
rewrite qsp_one_phase /qsp_step; cbn [fst snd].
rewrite expi_conj.
have h1 : expi a * expi (b+a) = expi (a+a+b).
  by rewrite -expiD; congr (expi _); ring.
have h2 : expi a * expi (a-b) = expi (a+a-b).
  by rewrite -expiD; congr (expi _); ring.
have h3 : expi (-a) * expi (b+a) = expi b.
  by rewrite -expiD; congr (expi _); ring.
have h4 : expi (-a) * expi (a-b) = expi (-b).
  by rewrite -expiD; congr (expi _); ring.
congr (_, _).
- transitivity (((expi a)%:P * (expi (b+a))%:P) * 'X^2 +
    ((expi a)%:P * (expi (a-b))%:P) * defect R); first by ring.
  by rewrite -!polyCM h1 h2.
- transitivity (((expi (-a))%:P * (expi (b+a))%:P -
    (expi (-a))%:P * (expi (a-b))%:P) * 'X); first by ring.
  by rewrite -!polyCM h3 h4 polyCB.
Qed.

Lemma qsp_example_degree_zero (c : R) : -1 <= c <= 1 ->
  qsp_pair [::] (acos c) = (((c +i* Num.sqrt (1-c^+2))%C)%:P, (0:poly)).
Proof. by move=>hc; rewrite /qsp_pair /expi (acos_def hc).2 sin_acos //. Qed.

Lemma qsp_example_degree_one_X :
  qsp_pair [:: (pi/4:R)] (-(pi/4)) = ('X, (-'i%C)%:P : poly).
Proof.
rewrite qsp_one_phase addrN expi0 polyC1 mul1r.
have H : (-(pi/4) - (pi/4) = -(pi/2) :> R) by rewrite -opprD quarter_double.
rewrite H /expi cosN sinN cos_pihalf sin_pihalf.
congr ('X, _%:P); by simpc.
Qed.
Lemma qsp_example_degree_one_zero :
  qsp_pair [:: (0:R)] (pi/2) = (('i%C)%:P * 'X, ('i%C)%:P : poly).
Proof. by rewrite qsp_one_phase add0r subr0 expi_pi_half. Qed.
Lemma qsp_example_degree_two_one :
  qsp_pair [:: (0:R); 0] 0 = (1, (0:poly)).
Proof.
rewrite /qsp_pair /qsp_step /= expi0 /= /defect cos0 sin0 oppr0 /= !polyC1.
congr (_, _); ring.
Qed.
Lemma expi_pi : expi (pi : R) = -1.
Proof. rewrite /expi cospi sinpi. by simpc. Qed.
Lemma expi_neg_pi_half : expi (-(pi/2) : R) = -'i%C.
Proof. rewrite /expi cosN sinN cos_pihalf sin_pihalf. by simpc. Qed.
Lemma qsp_example_degree_two_chebyshev :
  qsp_pair [:: (pi/4:R); -(pi/2)] (pi/4) =
  (2 *: ('X^2 : poly) - 1, (-(2:C) * 'i%C)%:P * 'X).
Proof.
rewrite qsp_symmetric_two_phase quarter_double addrN expi0 opprK
  expi_pi_half expi_neg_pi_half half_double expi_pi /defect !polyC1.
congr (_, _).
- have h2 : (2:C) = 1+1 by ring.
  rewrite h2 scalerDl !scale1r polyCN polyC1; ring.
- congr (_%:P * 'X); ring.
Qed.

Lemma sin_quarter : sin (pi/4 : R) = Num.sqrt 2 / 2.
Proof.
have harg : (pi/4 - pi/2 = -(pi/4) :> R).
  rewrite -quarter_double; ring.
have hcs : cos (pi/4:R) = sin (pi/4).
  by rewrite -(cosBpihalf (pi/4:R)) harg cosN.
have hs : 0 <= sin (pi/4:R).
  apply: sin_ge0_pi; apply/andP; split.
  - by rewrite divr_ge0 ?pi_ge0 // ler0n.
  - rewrite ler_pdivrMr ?ltr0Sn //.
    rewrite -{1}[pi]mulr1 ler_pM2l ?pi_gt0 //.
    by rewrite ler1n.
have hn := cos2Dsin2 (pi/4:R).
rewrite hcs in hn.
have hsq : (sin (pi/4:R) * 2)^+2 = 2.
  transitivity (2 * (sin (pi/4:R)^+2 + sin (pi/4)^+2)); first by ring.
  by rewrite hn mulr1.
have hh : sin (pi/4:R) * 2 = Num.sqrt 2.
  apply: sqr_inj; first by rewrite nnegrE mulr_ge0 // ler0n.
  - by rewrite nnegrE sqrtr_ge0.
  - by rewrite hsq sqr_sqrtr // ler0n.
by rewrite -hh mulfK // pnatr_eq0.
Qed.
Lemma eighth_double : (pi/8 + pi/8 = pi/4 :> R).
Proof.
rewrite -mulrDr -mulr2n -mulr_natr.
have h8 : (8:R)=4*2 by ring.
by rewrite h8 invfM -mulrA mulVf ?mulr1 // pnatr_eq0.
Qed.
Lemma expi_quarter_difference :
  expi (-(pi/4):R)-expi (pi/4) = -'i%C * (Num.sqrt 2)%:C.
Proof.
rewrite /expi cosN sinN sin_quarter; simpc.
by rewrite -opprD half_double.
Qed.
Lemma qsp_example_degree_two_square :
  qsp_pair [:: (pi/8:R); -(pi/4)] (pi/8) =
  (('X^2 : poly) + ('i%C)%:P * defect R,
    (-'i%C * (Num.sqrt 2)%:C)%:P * 'X).
Proof.
by rewrite qsp_symmetric_two_phase eighth_double addrN expi0 opprK
  quarter_double expi_pi_half polyC1 mul1r expi_quarter_difference.
Qed.
End Examples.
End QSVTExamples.

(* The scalar endpoint convention of EN-F.1.  A nonempty prefix means at
   least one reflection signal; endpoint absorption preserves P, and its
   precise effect on Q is retained. *)
Module QSVTEndpointConvention.
Import Order.TTheory GRing.Theory Num.Def Num.Theory complex trigo QSVTPolynomial.
Local Open Scope ring_scope.
Section Endpoint.
Variable R : realType.
Local Notation C := R[i].
Local Notation poly := {poly C}.
Definition scale_pair (z:C) (pq:poly*poly) :=
  (z%:P * pq.1,z%:P * pq.2).
Lemma qsp_step_scale phi z pq :
  qsp_step phi (scale_pair z pq) = scale_pair z (qsp_step phi pq).
Proof.
case: pq=>p q; rewrite /qsp_step /scale_pair; cbn [fst snd]; congr (_, _); ring.
Qed.

(* A shift of the last phase multiplies the entire first column uniformly. *)
Lemma qsp_pair_last_shift prefix last t :
  qsp_pair prefix (last+t) = scale_pair (expi t) (qsp_pair prefix last).
Proof.
elim: prefix=>[|a middle IH]; last by rewrite /= IH qsp_step_scale.
change (((expi (last+t))%:P,0) =
  ((expi t)%:P * (expi last)%:P,(expi t)%:P * (0:poly))).
by rewrite -polyCM -expiD [t+last]addrC mulr0.
Qed.

(* A shift of the first phase acts with opposite signs on the two rows. *)
Lemma qsp_step_phase_shift (a t:R) pq :
  qsp_step (a+t) pq =
  ((expi t)%:P * (qsp_step a pq).1,
    (expi (-t))%:P * (qsp_step a pq).2).
Proof.
case: pq=>p q; rewrite /qsp_step; cbn [fst snd].
rewrite !expi_conj expiD opprD expiD !polyCM.
congr (_, _); ring.
Qed.

Theorem qsvt_endpoint_corner_bridge (a last:R) middle :
  qsp_pair ((a+last)::middle) 0 =
  ((qsp_pair (a::middle) last).1,
    (expi (-(last+last)))%:P * (qsp_pair (a::middle) last).2).
Proof.
have hlast := qsp_pair_last_shift middle (0:R) last.
rewrite add0r in hlast.
change (qsp_step (a+last) (qsp_pair middle 0) =
  ((qsp_step a (qsp_pair middle last)).1,
    (expi (-(last+last)))%:P * (qsp_step a (qsp_pair middle last)).2)).
rewrite hlast qsp_step_scale qsp_step_phase_shift /scale_pair; cbn [fst snd].
have he : expi (-(last+last)) * expi last = expi (-last).
  by rewrite -expiD; congr (expi _); ring.
congr (_, _).
by rewrite mulrA -polyCM he.
Qed.

Corollary qsvt_endpoint_selected_polynomial (a last:R) middle :
  (qsp_pair ((a+last)::middle) 0).1 = (qsp_pair (a::middle) last).1.
Proof. by rewrite qsvt_endpoint_corner_bridge. Qed.
End Endpoint.
End QSVTEndpointConvention.

Module QSVTRejectedParity.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Section Example.
Variable R : realType.
Definition mixed_parity_example : {poly R} := (2:R)^-1 *: (1+'X).
Theorem mixed_parity_not_admissible d :
 ~ QSVTRealPair.admissible d mixed_parity_example.
Proof.
move=>[_ [hp _]].
have h0 : mixed_parity_example`_0 = (2:R)^-1.
 by rewrite /mixed_parity_example coefZ coefD coef1 coefX /= addr0 mulr1.
have h1 : mixed_parity_example`_1 = (2:R)^-1.
 by rewrite /mixed_parity_example coefZ coefD coef1 coefX /= add0r mulr1.
have hn : (2:R)^-1 != 0 by rewrite invr_eq0 pnatr_eq0.
case hd : (odd d).
- have hbad : odd 0 != odd d by rewrite hd.
  by move: hn; rewrite -h0 (hp 0 hbad) eqxx.
- have hbad : odd 1 != odd d by rewrite hd.
  by move: hn; rewrite -h1 (hp 1 hbad) eqxx.
Qed.
End Example.
End QSVTRejectedParity.
