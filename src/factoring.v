From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory GRing Num.Theory Order.Theory.
(* Local Open Scope ring_scope.
Local Open Scope quotient_scope. *)

Section ContFraction.
Import FracField.

Section Util.

Implicit Type s u v: seq nat.
Implicit Type p q: int.
Implicit Type x y: rat.

Lemma eq_properfrac p q x y
  (H: (p%:Q + x)%R = (q%:Q + y)%R)
  (Hxge0: (0 <= x)%R) (Hxlt1: (x < 1)%R)
  (Hyge0: (0 <= y)%R) (Hylt1: (y < 1)%R):
    x = y.
Proof.
  have Heq: ((p - q)%:Q%R = (y - x)%R) by
    rewrite mulrzBr addrC -[RHS](addKr (q%:Q)%R);
    f_equal; rewrite addrA -H addrK.
  case /intP Hpq: (p - q)%R => [|n|n].
  - move: Heq;
    rewrite Hpq mulr0z => Hxy.
    by rewrite -[RHS](addrNK x) -Hxy add0r.
  - have: ((y - x) < 1)%R
      by apply: ltr_wnDr; rewrite ?oppr_le0.
    by rewrite -Heq Hpq -{2}(mulr1z 1) ltr_int.
  - have: (-1 < (y - x))%R
      by apply: ltr_wpDl; rewrite ?ltrN2.
    by rewrite -Heq Hpq -(mulrN1z 1) ltr_int.
Qed.

Lemma eq_floorint p q x y
  (H: (p%:Q + x)%R = (q%:Q + y)%R)
  (Hxge0: (0 <= x)%R) (Hxlt1: (x < 1)%R)
  (Hyge0: (0 <= y)%R) (Hylt1: (y < 1)%R):
    p = q.
Proof.
  have: ((p - q)%:Q%R = (y - x)%R) by
    rewrite mulrzBr addrC -[RHS](addKr (q%:Q)%R);
    f_equal; rewrite addrA -H addrK.
  have ->: x = y by apply: (eq_properfrac H).
  rewrite addrN -(mulr0z 1);
  move => /intr_inj; exact: subr0_eq.
Qed.

Lemma eq_int_dem p q x y
  (H: (p%:Q + x)%R = (q%:Q + y)%R)
  (Hxge0: (0 <= x)%R) (Hxlt1: (x < 1)%R)
  (Hyge0: (0 <= y)%R) (Hylt1: (y < 1)%R):
    p = q /\ x = y.
Proof.
  split.
  - by apply: (eq_floorint H).
  - by apply: (eq_properfrac H).
Qed.

Lemma pngt0 x:
  (x > 0)%R ->
  let: (@Rat (nx,dx) _) := x in
  (nx > 0)%R.
Proof.
  have ->: (x > 0)%R = lt_rat zeroq x by [].
  move: x => [[nx dx] prf] /=.
  by rewrite mul0r mulr1.
Qed.

Lemma pnge0 x:
  (x >= 0)%R ->
  let: (@Rat (nx,dx) _) := x in
  (nx >= 0)%R.
Proof.
  have ->: (x >= 0)%R = le_rat zeroq x by [].
  move: x => [[nx dx] prf] /=.
  by rewrite mul0r mulr1.
Qed.

Lemma gt0_lt0f (R: numDomainType) (x: R):
  (0 < x)%R -> (x < 0)%R = false.
Proof.
  move => P1. apply /negP.
  move => /(lt_trans P1).
  by rewrite ltxx.
Qed.

Lemma ge0_lt0f (R: numDomainType) (x: R):
  (0 <= x)%R -> (x < 0)%R = false.
Proof.
  move => P1. apply /negP.
  move => /(le_lt_trans P1).
  by rewrite ltxx.
Qed.

Lemma gcdzMDr q m n : gcdz (q * m + n) m = gcdz n m.
Proof. by rewrite -gcdz_modl modzMDl gcdz_modl. Qed.

Lemma mulz_sign_absP_modn (a: int) (b: nat):
  (0 <= a)%R -> ((-1) ^+ (a < 0)%R * Posz (`|a| %/ b))%R = (a %/ Posz b)%Z.
Proof.
  move => Ha.
  have ->: Posz (`|a| %/ b) = `|(a %/ Posz b)%Z|.
  move: b => [|b]; first by rewrite divn0 divz0.
  move: a Ha => [a|a];
  by rewrite /divz /= ?mul1n ?PeanoNat.Nat.add_0_r.
  have ->: (a < 0)%R = ((a %/ b)%Z < 0)%R.
  rewrite (ge0_lt0f Ha) ge0_lt0f //.
  move: b => [|b]; by rewrite ?divz0 ?divz_ge0.
  exact: mulz_sign_abs.
Qed.

Lemma numq_addn x (h: nat):
  (0 <= x)%R -> numq (h%:~R + x)%Q = (Posz h * denq x + numq x)%R.
Proof.
  move: x => [[nx dx] /= prf] /pnge0 Hn;
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in (_ + (numq X))%R]valqK num_fracq
   -[X in (denq X)]valqK den_fracq addq_def addq_subdefE /=.
  have ->: (valq h%:~R).1 = h
    by rewrite -{2}(numq_int h).
  have ->: (valq h%:~R).2 = 1%R
    by rewrite -(denq_int h).
  rewrite mul1r mulr1 num_fracq /= gt0_lt0f -?exprnP //=.
  have ->: (dx != 0)%R by apply lt0r_neq0.
  have ->: gcdn `|(Posz h * dx + nx)%R| `|dx| = `|gcdz nx dx|
    by rewrite -(gcdzMDr (Posz h)) /gcdz.
  have Hdvd: (gcdn `|nx| `|dx| %| dx)%Z by exact: dvdn_gcdr.
  rewrite !mulz_sign_absP_modn //.
  rewrite divzDl /= -?mulz_divA -?divz_nat ?gtz0_abs //.
  by apply: dvdz_mull.
  by rewrite ler_wpDr // pmulr_lge0.
Qed.

Lemma denq_addn x (h: nat):
  (0 <= x)%R -> denq (h%:~R + x)%Q = denq x.
Proof.
  move: x => [[nx dx] /= prf] /pnge0 Hn;
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in _ = denq X]valqK den_fracq addq_def addq_subdefE /=.
  have ->: (valq h%:~R).1 = h
    by rewrite -{2}(numq_int h).
  have ->: (valq h%:~R).2 = 1%R
    by rewrite -(denq_int h).
  rewrite mul1r mulr1 den_fracq /=.
  by have ->: gcdn `|(Posz h * dx + nx)%R| `|dx| = `|gcdz nx dx|
    by rewrite -(gcdzMDr (Posz h)) /gcdz.
Qed.

Lemma denq_inv x:
  (x > 0)%R -> denq (x^-1%Q) = numq x.
Proof.
  move => Hgt0.
  move: Hgt0 {+}Hgt0 => /lt0r_neq0 +/pngt0.
  move: x => [[nx dx] /= prf] /=.
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in (X != 0%Q)]valqK fracq_eq0 negb_or /=
    den_fracq /= -[X in (numq X)]valqK num_fracq /=.
  move => /andP [H1 H2] Hn.
  by rewrite H2 H1 /= -exprnP signr_addb
    (gt0_lt0f Hn) (gt0_lt0f Hd) expr0 !mul1r gcdnC.
Qed.

Lemma numq_inv x:
  (x > 0)%R -> numq (x^-1%Q) = denq x.
Proof.
  move => Hgt0.
  move: Hgt0 {+}Hgt0 => /lt0r_neq0 +/pngt0.
  move: x => [[nx dx] /= prf] /=.
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in (X != 0%Q)]valqK fracq_eq0 negb_or /=
    num_fracq /= -[X in (denq X)]valqK den_fracq /=.
  move => /andP [H1 H2] Hn.
  by rewrite H2 H1 /= -exprnP signr_addb
    (gt0_lt0f Hn) (gt0_lt0f Hd) expr0 !mul1r gcdnC.
Qed.

Lemma rat_eqP x y:
  reflect (numq x = numq y /\ denq x = denq y) (x == y).
Proof.
  apply: (iffP idP) => [/eqP ->//|[/eqP Hn /eqP Hd]].
  by rewrite rat_eqE Hn Hd.
Qed.

End Util.

Section Seq2Rat.

Implicit Type u: seq nat.
Implicit Type n: nat.

(* numbers in seq satisfy (leq 1) *)
Fixpoint s2r_pair n u: nat * nat :=
  match n, u with
  | _, [::] | O, _ => (0, 1)
  | S n, h :: t =>
    ((s2r_pair n t).2, h.+1 * (s2r_pair n t).2 + (s2r_pair n t).1)
  end.

Lemma s2r_subproof n u :
  let v := ((s2r_pair n u).1 %:Z%Z, (s2r_pair n u).2 %:Z%Z) in
  (0%Z < v.2)%R && coprime `|v.1| `|v.2|.
Proof.
  apply /andP.
  rewrite !absz_nat ltz_nat;
  elim: n u => [|n' IHn] [|h t] //=;
  pose nn := (s2r_pair n' t).1;
  pose dd := (s2r_pair n' t).2.
  split.
  - by apply: ltn_addr;
    rewrite muln_gt0 (proj1 (IHn t)).
  - by rewrite -coprime_modr modnMDl
    coprime_sym coprime_modl (proj2 (IHn t)).
Qed.

Definition s2r_ n u: rat := Rat (s2r_subproof n u).
Definition s2r u := s2r_ (size u) u.

Lemma s2r__nil n: s2r_ n [::] = 0%Q.
Proof.
  by case: n =>[|n];
  apply /eqP /rat_eqP; split.
Qed.

Lemma s2r__0 u: s2r_ 0 u = 0%Q.
Proof.
  by case: u => [|h t];
  apply /eqP /rat_eqP; split.
Qed.

Lemma denq_s2r__rec n h t:
  denq (s2r_ n.+1 (h::t)) = (h.+1%:Z * denq (s2r_ n t) + numq (s2r_ n t))%R.
Proof. by []. Qed.

Lemma numq_s2r__rec n h t:
  numq (s2r_ n.+1 (h::t)) = denq (s2r_ n t).
Proof. by []. Qed.

Lemma s2r__rec n h t:
  s2r_ n.+1 (h :: t) = ((h.+1%:Q + s2r_ n t)^-1)%R.
Proof.
  apply /eqP.
  rewrite rat_eq denq_s2r__rec numq_s2r__rec.
  have H1: (0 < (h.+1%:~R + s2r_ n t)%Q)%R
    by rewrite ltr_wpDr ?ltr0Sn.
  by rewrite numq_inv ?denq_inv ?numq_addn ?denq_addn.
Qed.

Lemma s2r__gt0 n h t:
  (s2r_ n.+1 (h::t) > 0)%R.
Proof.
  by rewrite s2r__rec invr_gt0 ltr_wpDr ?ltr0Sn.
Qed.

Lemma s2r__gt0_iff n u:
  if n is O then s2r_ n u = 0%R
    else if u is [::] then s2r_ n u = 0%R
      else (s2r_ n u > 0)%R.
Proof.
  move: n u => [|n'] [|h t];
  last (by exact: s2r__gt0);
  by apply /eqP /rat_eqP; split.
Qed.

Lemma s2r_lt1 n u:
  nth 0 u n != 0 -> (s2r_ n.+1 u < 1)%R.
Proof.
  case: n u => [|n] [|h t] //= H.
  - rewrite s2r__rec invf_lt1;
    by apply ltr_wpDr;
    rewrite ?(ltr1z, ltr0z) // ltz_nat ltnS lt0n.
  - rewrite s2r__rec invf_lt1;
    apply ltr_pwDr;
    rewrite ?(ler1z, ler0z) //;
    (by case: t H => [|h' t' H];
    [rewrite nth_nil| apply: s2r__gt0]).
Qed.

Definition rat_s2r__rec :=
  (s2r__nil, s2r__0, denq_s2r__rec, numq_s2r__rec, s2r__rec).

Lemma s2r__recl n u:
  n.+1 < size u ->
  numq (s2r_ n.+2 u) =
    ((nth 0%N u n.+1).+1%:Z * numq (s2r_ n.+1 u) + numq (s2r_ n u))%R /\
  denq (s2r_ n.+2 u) =
    ((nth 0%N u n.+1).+1%:Z * denq (s2r_ n.+1 u) + denq (s2r_ n u))%R.
Proof.
  elim: n u => [|n' IHn] [|h [|h' [|h'' t2]]] // Hu.
  1, 2: by rewrite /s2r /denq /numq /= !muln1 !addn0
    mulr1 addr0 PoszD PoszM mulrC.
  have ->: nth 0%N [:: h, h', h'' & t2] n'.+2
    = nth 0%N [:: h', h'' & t2] n'.+1 by [].
  split;
  [rewrite [numq (_ n'.+1 _)]numq_s2r__rec;
  rewrite [numq (_ n'.+2 _)]numq_s2r__rec;
  rewrite [numq (_ n'.+3 _)]numq_s2r__rec
  |rewrite [denq (_ n'.+1 _)]denq_s2r__rec;
  rewrite [denq (_ n'.+2 _)]denq_s2r__rec;
  rewrite [denq (_ n'.+3 _)]denq_s2r__rec].
  by apply: proj2 (IHn _ _).
  rewrite (proj1 (IHn _ _)) // (proj2 (IHn _ _)) //
    !mulrDr !addrA; f_equal;
  rewrite addrC addrA; f_equal;
  rewrite addrC; f_equal;
  by rewrite -mulrCA.
Qed.

Lemma s2r__prefix n u v :
  n <= size u ->
    s2r_ n (u ++ v) = s2r_ n u.
Proof.
  elim: n u => [|n' IHn] [|h t] //=.
  1, 2: by rewrite !rat_s2r__rec.
  rewrite !s2r__rec ltnS => H.
  f_equal; f_equal; exact: IHn.
Qed.

Lemma s2r_prefix u v:
  s2r_ (size u) (u ++ v) = s2r u.
Proof.
  exact: s2r__prefix.
Qed.

Lemma s2r__inj u v n:
  s2r_ n.+1 u = s2r_ n.+1 v ->
  nth O u n != O ->
  nth O v n != O ->
  take n.+1 u = take n.+1 v.
Proof.
  elim: n u v => [|n IHn]
    [|hu [|hu' tu']] [|hv [|hv' tv']] //=;
  rewrite !s2r__rec ?s2r__0 ?s2r__nil ?addr0 ?nth_nil;
  move => /invr_inj //;
  try (
    by move => /intr_inj /eqP;
    rewrite eqz_nat eqSS;
    move => /eqP Huv _ _;
    rewrite Huv
  ).
  rewrite -!(s2r__rec n);
  move => Heq Hnu Hnv.
  have Int_Dem: (hu.+1%:Z = hv.+1%:Z)%R
      /\ s2r_ n.+1 (hu' :: tu') = s2r_ n.+1 (hv' :: tv')
  by exact: (eq_int_dem Heq _ (s2r_lt1 Hnu) _ (s2r_lt1 Hnv)).
  f_equal.
  - by apply /eqP;
    rewrite -(inj_eq succn_inj) -eqz_nat (proj1 Int_Dem).
  - by rewrite -!(take_cons n.+1) (IHn _ (hv'::tv')) ?(proj2 Int_Dem).
Qed.

End Seq2Rat.

Section Rat2Seq.

Implicit Type u v: seq nat.
Implicit Type x y: rat.

(* Does end with 1 *)
Fixpoint r2s1_rec (p q: nat) : seq nat :=
  if (p == 0) || (q == 0) then [::] else
  let p' := q %% p in if p' is O then (q %/ p).-2 :: [:: O] else
  if p - (p'.-1) is (q'.+1) then (q %/ p).-1 :: (p %/ p').-1 ::
    r2s1_rec (q' %% p') p' else [::].

Definition r2s1 x := r2s1_rec (`|numq x|%%`|denq x|) `|denq x|.

Definition cast_s u :=
  match lastP u with
  | LastNil => u
  | LastRcons s x => 
    match lastP s, x with
    | LastRcons s' x', O => rcons s' x'.+1
    | _, _ => u
    end
  end.

Definition cast_l u :=
  match lastP u with
  | LastNil => u
  | LastRcons s x =>
    match x with
    | O => u 
    | S x' => rcons (rcons s x') O
    end
  end.

(* Does not end with 1 *)
Definition r2s x := cast_s (r2s1 x).

Definition I01 x := (0 <= x /\ x < 1)%R.

Definition r2s_odd x :=
  if odd (size (r2s1 x)) then r2s1 x else r2s x.

Definition r2s_even x :=
  if odd (size (r2s1 x)) then r2s x else r2s1 x.

Variable x y: rat.

Local Notation "'p_' n" := (numq (s2r_ (n) (r2s1 y))) (at level 2).
Local Notation "'q_' n" := (denq (s2r_ (n) (r2s1 y))) (at level 2).
Local Notation "'y_' n" :=  (s2r_ (n) (r2s1 y)) (at level 2).

End Rat2Seq.

End ContFraction.
