(* Classical arithmetic used by Shor's factor extraction, Lemma 7.2(1).
   The canonical-residue argument is in CASE-STUDIES.md. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorArithmetic.

Definition nontrivial_factor N d := (1 < d < N) && (d %| N).

Lemma nontrivial_sqrt_factor N s :
  1 < s -> s + 1 < N -> s ^ 2 == 1 %[mod N] ->
  nontrivial_factor N (gcdn (s - 1) N).
Proof.
move=>Hs HN Hsq.
have Hs0 : 0 < s - 1 by rewrite subn_gt0.
have Hs1 : 1 <= s := ltnW Hs.
have Hss : 1 <= s ^ 2 by rewrite -[1](exp1n 2) leq_sqr.
have Dprod : N %| (s - 1) * (s + 1).
  by rewrite -subn_sqr exp1n -(eqn_mod_dvd N Hss).
have Hcop : ~~ coprime N (s - 1).
  apply/negP=>Hc.
  have Dplus : N %| s + 1 by move: Dprod; rewrite Gauss_dvdr.
  have Hplus : 0 < s + 1 by rewrite addn1.
  have Hle := dvdn_leq Hplus Dplus.
  by move: (leq_ltn_trans Hle HN); rewrite ltnn.
have Hg0 : 0 < gcdn (s - 1) N by rewrite gcdn_gt0 Hs0.
have Hg1 : 1 < gcdn (s - 1) N.
  by rewrite ltn_neqAle eq_sym -/(coprime (s - 1) N) coprime_sym Hcop Hg0.
have Hgle : gcdn (s - 1) N <= s - 1 := dvdn_leq Hs0 (dvdn_gcdl _ _).
have Hsmall : s - 1 < N.
  apply: leq_ltn_trans HN.
  exact: leq_trans (leq_subr 1 s) (leq_addr 1 s).
rewrite /nontrivial_factor Hg1 (leq_ltn_trans Hgle Hsmall) /=.
exact: dvdn_gcdr.
Qed.

Lemma nontrivial_sqrt_factor_mod N s :
  1 < N -> 1 < s %% N -> s %% N + 1 < N ->
  s ^ 2 == 1 %[mod N] -> nontrivial_factor N (gcdn (s - 1) N).
Proof.
move=>HN Hr HrN Hsq.
have HN0 : 0 < N := ltnW HN.
have Hr1 : 1 <= s %% N := ltnW Hr.
have Hs1 : 1 <= s := leq_trans Hr1 (leq_mod s N).
have Hr0 : (s %% N < 1) = false by rewrite ltnNge Hr1.
have Epred : (s - 1) %% N = s %% N - 1.
  by rewrite modnB // (@modn_small 1 N HN) Hr0 mul0n add0n.
rewrite -gcdn_modl Epred.
apply: nontrivial_sqrt_factor=>//.
by rewrite modnXm.
Qed.

(* The paper's continued-fraction selector, with an explicit failure result.
   A positive rational denominator supplies enough Euclidean steps. *)
Fixpoint convergents fuel a b : seq (nat * nat) :=
  if fuel is fuel'.+1 then
    if b == 0 then [::] else
      let q := a %/ b in
      (q, 1) :: map (fun pd => (q * pd.1 + pd.2, pd.1))
        (convergents fuel' b (a %% b))
  else [::].

Lemma convergents_stable fuel a b extra : b <= fuel ->
  convergents (fuel + extra) a b = convergents fuel a b.
Proof.
elim: fuel a b=>[a b|fuel IH a b] Hb.
- have -> : b = 0 by apply/eqP; move: Hb; rewrite leqn0.
  by rewrite add0n; case: extra.
- rewrite addSn /=; case Eb: (b == 0)=>//.
  congr (_ :: _); congr (map _ _).
  apply: IH.
  have Hb0 : 0 < b by rewrite lt0n Eb.
  exact: leq_trans (ltn_pmod a Hb0) Hb.
Qed.

Definition approximation_test a b (pd : nat * nat) :=
  (0 < pd.2) &&
  (2 * pd.2 * ((pd.1 * b - a * pd.2) + (a * pd.2 - pd.1 * b)) < b).

Definition printed_postprocess a b :=
  match map snd (filter (approximation_test a b) (convergents b.+1 a b)) with
  | [::] => None
  | d :: ds => Some (foldr minn d ds)
  end.

Lemma printed_quarter_counterexample : printed_postprocess 1 4 = Some 1.
Proof. by vm_compute. Qed.

Lemma printed_three_quarters_counterexample : printed_postprocess 3 4 = Some 1.
Proof. by vm_compute. Qed.

Lemma two_mod_fifteen_order :
  (2 ^ 4 == 1 %[mod 15]) /\
  (forall k, 0 < k < 4 -> ~~ (2 ^ k == 1 %[mod 15])).
Proof.
split; first by vm_compute.
case=>[//|[|[|[|k]]]] //=.
Qed.

End ClassicalShorArithmetic.
