From mathcomp Require Import all_ssreflect.
Require Import Lia.

(****************************************************************************)
(* Light-weight tactic for mathcomp nat based on standard Lia/Nia: dealing  *)
(* with ordinal numbers, divn, modn, half/uphalf and bump. It served as the *)
(* automated checking for the disjointness of quantum registers (of array   *)
(* variables with indexes).                                                 *)
(* ------------------------------------------------------------------------ *)
(* * Tactics :                                                              *)
(*    AutoNat.move_all : move all the hypothesis to goal                    *)
(*    AutoNat.move_ord : move all the hypothesis and variables to stack;    *)
(*                       elim == and = of ord                               *)
(*    AutoNat.elim_odd : eliminate "odd n"                                  *)
(*    AutoNat.elim_div : eliminate "div.divn x y"                           *)
(*    AutoNat.elim_mod : eliminate "div.modn x y"                           *)
(*   AutoNat.elim_bump : deal with fintype.bump, by case analysis           *)
(*                                                                          *)
(*      mc_nat_convert : simplify expressions for ordinal numbers           *)
(*              mc_nat : after mc_nat_convert, use Lia.nia to solve         *)
(* Use "time mc_nat" to automatically solve lemmas about ordinal numbers    *)
(****************************************************************************)

Module AutoNatTheory.

Section PreprocessingTheory.

(* computation *)
Lemma R1 : muln = Nat.mul.
Proof. by []. Qed.

Lemma R2 : addn = Nat.add.
Proof. by []. Qed.

Lemma R3 : subn = Nat.sub.
Proof. by []. Qed.

Lemma R5 m n : divn m n = Nat.div m n.
Proof.
case: n=>[|n]; first by rewrite/= divn0.
move: (divn_eq m n.+1) (PeanoNat.Nat.div_mod_eq m n.+1)=>{1}->.
rewrite -R2 -R1 mulnC.
set a1 := m %/ n.+1.
set a2 := PeanoNat.Nat.div m n.+1.
set b1 := m %% n.+1.
set b2 := PeanoNat.Nat.modulo m n.+1.
move=>P1; apply/anti_leq/andP; split.
- rewrite leqNgt -(@leq_pmul2l n.+1)// -(@leq_add2r b1).
  rewrite P1 -ltnNge mulnS [n.+1 + _ ]addnC -addnA ltn_add2l.
  by apply/ltn_addr/ltP/PeanoNat.Nat.mod_upper_bound.
- rewrite leqNgt -(@leq_pmul2l n.+1)// -(@leq_add2r b2).
  rewrite -P1 -ltnNge mulnS [n.+1 + _ ]addnC -addnA ltn_add2l.
  by apply/ltn_addr/ltn_pmod.
Qed.

Lemma R41 n : uphalf n = divn n.+1 2.
Proof. by rewrite uphalfE -divn2. Qed.
Lemma R40 n : half n = divn n 2.
Proof. by rewrite -divn2. Qed.
Lemma R42 n : double n = 2 * n.
Proof. by rewrite mul2n. Qed.
Lemma R43 n t : n = 2 * t ->
  (divn n 2 = t) * (divn n.+1 2 = t) * 
  (divn n.+2 2 = t.+1) * (divn n.+3 2 = t.+1) *
  (modn n 2 = 0) * (modn n.+1 2 = 1) *
  (modn n.+2 2 = 0) * (modn n.+3 2 = 1).
Proof.
by rewrite mul2n=>->; rewrite -!R40 -!doubleS 
  !doubleK -!uphalfE !uphalf_double !modn2/= odd_double.
Qed.
Lemma R44 n t : n = (2 * t).+1 ->
  (divn n.-1 2 = t) *
  (divn n 2 = t) * (divn n.+1 2 = t.+1) * 
  (divn n.+2 2 = t.+1) * (divn n.+3 2 = t.+2) *
  (modn n.-1 2 = 0) *
  (modn n 2 = 1) * (modn n.+1 2 = 0) *
  (modn n.+2 2 = 1) * (modn n.+3 2 = 0).
Proof.
by rewrite mul2n=>->; rewrite -!R40 -!doubleS 
  !doubleK -!uphalfE !uphalf_double !modn2/= odd_double.
Qed.

Lemma R45 n : odd n = true -> exists t, n = (2 * t).+1.
Proof. by move=>Po; exists n./2; rewrite mul2n -[LHS]odd_double_half Po. Qed.
Lemma R46 n : odd n = false -> exists t, n = 2 * t.
Proof. by move=>Po; exists n./2; rewrite mul2n -[LHS]odd_double_half Po. Qed.

Definition R4 := (R41,R40,R42).

(* Lemma R4 : half = (Nat.div ^~ 2).
Proof. by apply/funext=>i; rewrite -divn2 R5. Qed. *)

Lemma R6 m n : modn m n = Nat.modulo m n.
Proof.
move: (divn_eq m n) (PeanoNat.Nat.div_mod_eq m n)=>{1}->.
by rewrite -R2 -R5 -R1 mulnC=>/addnI.
Qed.

Lemma R7 m n : minn m n = Nat.min m n.
Proof. by case: (leqP m n)=>[/leP/min_l->|/ltnW/leP/min_r->]. Qed.

Lemma R8 m n : maxn m n = Nat.max m n.
Proof. by case: (leqP m n)=>[/leP/max_r->|/ltnW/leP/max_l->]. Qed.

Definition Rm := (R1, R2, R3, R5, R6, R7, R8).

(* is_true *)
Lemma Q0 : false -> False. Proof. by []. Qed.

Lemma Q01 (n : 'I_0) (P : Prop) : P. Proof. by case: n. Qed.
Lemma Q02 n (H : lt n 0) (P : Prop) : P. 
Proof. by exfalso; apply (PeanoNat.Nat.nlt_0_r n). Qed.

Lemma Q1 (a b : bool) : 
  (is_true (a || b)) <-> is_true a \/ is_true b.
Proof. by split=>/orP. Qed.

Lemma Q2 (a b : bool) :
  is_true (a && b) <-> is_true a /\ is_true b.
Proof. by split=>/andP. Qed.

Lemma Q3 (a b : bool) :
  is_true (a ==> b) <-> (is_true a -> is_true b).
Proof. by split=>/implyP. Qed.

Lemma Q5 (a : bool) :
  is_true (~~ a) <-> ~ (is_true a).
Proof. by split=>/negP. Qed.

Lemma Q41 (a : bool) :
  a = false <-> ~ (is_true a).
Proof. by rewrite -Q5; split=>/negPf->. Qed.

Lemma Q42 (a : bool) :
  a = true <-> (is_true a).
Proof. by []. Qed.

Lemma Q43 (a : bool) :
  false = a <-> ~ (is_true a).
Proof. by rewrite -Q41. Qed.

Lemma Q44 (a : bool) :
  true = a <-> (is_true a).
Proof. by rewrite -Q42. Qed.

Lemma Q45 (x y : bool) :
  (x = y) <-> (is_true x <-> is_true y).
Proof. exact: Bool.eq_iff_eq_true. Qed.

Definition Qm := (Q41, Q42, Q43, Q44, Q45, Q1, Q2, Q3, Q5).

(* nat *)
Lemma Q6 (x y : nat) : 
  is_true (x < y) <-> (x < y)%coq_nat.
Proof. by split=>/ltP. Qed.

Lemma Q7 (x y : nat) :
  is_true (x <= y) <-> (x <= y)%coq_nat.
Proof. by split=>/leP. Qed.

Lemma Q8 (x y : nat) :
  is_true (x == y) <-> x = y.
Proof. by split=>/eqP. Qed.

Lemma Q9 (x y : nat) :
  is_true (x != y) <-> x <> y.
Proof. by split=>/eqP. Qed.

Definition Qnat := (Q6, Q7, Q8, Q9).

(* ord *)
Lemma Q10 (n : nat) (i j : 'I_n) :
  (i == j) = (nat_of_ord i == nat_of_ord j).
Proof. by rewrite (inj_eq (@ord_inj _)). Qed.

Lemma Q11 (n : nat) (i j : 'I_n) :
  (i = j) <-> (nat_of_ord i = nat_of_ord j).
Proof. by split=>[/(f_equal val)|/ord_inj]. Qed.

Definition Qord := (lift0, lift_max, Q10, Q11).

(* simple case for divn and modn *)
Lemma Q13 x : divn x 0 = 0.
Proof. by []. Qed.

Lemma Q14 x : modn x 0 = x.
Proof. by []. Qed.

End PreprocessingTheory.

End AutoNatTheory.

Module AutoNat.

(* move all hyp to goal *)
Ltac move_all := repeat match goal with
  | [n : _ |- _ ] => move : n; try clear n
end; rewrite ? AutoNatTheory.R4 /= ? AutoNatTheory.Qord /= .

(* move all hyp and var to stack; elim == and = of ord *)
Ltac move_ord := repeat match goal with
  | [ |- _ -> _ ] =>
    intro; rewrite ? AutoNatTheory.R4 /= ? AutoNatTheory.Qord /=
  | [ |- forall _, _ ] =>
    intro; rewrite ? AutoNatTheory.R4 /= ? AutoNatTheory.Qord /=
  end.

(* eliminate odd n by introducing t, such that n = 2 * t or (2 * t).+1 *)
(* further simplify trivial cases such as divn n 2 --> t by rewriting R43/R44 *)
(* we finally move the hyp to the goal for further possible elimination *)
Ltac elim_odd :=
  let o := fresh "_is_odd_" in
  let E := fresh "_case_odd_" in
  let t := fresh "half_" in
  let Pt := fresh "_halfP_" in
  set o := ssrnat.odd _;
  match goal with
  | [o := ssrnat.odd ?x |- _ ] => 
    case E: o=>/=;
    [ (try move=>/AutoNatTheory.Q0 []);
      move: E=>/AutoNatTheory.R45[t Pt];
      rewrite ?(@AutoNatTheory.R44 _ _ Pt)/= ?Pt
    | (try move=>/AutoNatTheory.Q0 []);
      move: E=>/AutoNatTheory.R46[t Pt];
      rewrite ?(@AutoNatTheory.R43 _ _ Pt)/= ?Pt
    ];
    clear o; (try clear x Pt); try move: Pt
  end.

(* Goal forall n, odd n -> ~~(odd n.+1) -> n %% 2 = 1.
Proof. move=>/= n; elim_odd. by []. Qed. *)


(* deal with div.divn x y *)
(* if y is already _.+1, we directly introduce the quotient q and remainder r *)
(*   such that x = y * q + s, s < y, and replacing divn x y --> q, modn x y --> r *)
(*   and further all occurence of x --> y * q + s *)
(* otherwise, we do case analysis on y, i.e., y = 0 or y = _.+1 *)
(*   if y = 0, replacing divn x y --> 0, modn x y --> x *)
(*   if y = _.+1, similar to above case *)
(* finally, we move all new hyp back to goal for further elimination *)
Ltac elim_div := 
  let q := fresh "quotient_" in
  let r := fresh "remainder_" in
  set q := div.divn _ _;
  match goal with
  | [q := div.divn ?x (S ?y) |- _ ] => 
    let x_t := fresh "_dividend_" in 
    let divP := fresh "_divP_" in 
    set r := div.modn x (S y);
    set x_t := x; 
    move: (div.divn_eq x (S y)); rewrite - {1} [x] /x_t => divP;
    rewrite ? divP /x_t ; clear x_t divP;
    (have : lt r (S y) by apply/ssrnat.ltP/div.ltn_pmod);
    move: (div.divn_eq x (S y)); rewrite - ? /q - ? /r /=;
    move: q r; intros ? ?;
    rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=
  | [t := div.divn ?x ?y |- _ ] => 
    let y_t := fresh "divisor_" in
    let Ey := fresh "_divisorE_" in
    set y_t := y in q *;
    (have: y_t = y by []);
    (have: q = div.divn x y_t by []);
    move: y_t q; case; 
    [ move => q; rewrite ? AutoNatTheory.Q13 ? AutoNatTheory.Q14 => ->;
      clear q
    | let Eq := fresh "_quotientE_" in
      let x_t := fresh "_dividend_" in
      let divP := fresh "_divP_" in
      move => y_t q /[swap] Ey Eq;
      set r := div.modn x (S y_t);
      set x_t := x;
      move: (div.divn_eq x (S y_t)); rewrite - {1} [x] /x_t => divP;
      rewrite ? divP /x_t; clear x_t divP;
      (have : lt r (S y_t) by apply/ssrnat.ltP/div.ltn_pmod);
      move: (div.divn_eq x (S y_t)); rewrite - ? Eq - ? /r /=;
      move: r Ey; clear Eq; intros ?;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=
    ]
  end.

(* deal with div.modn, similar to div.divn *)
Ltac elim_mod := 
  let r := fresh "remainder_" in
  let q := fresh "quotient_" in
  set r := div.modn _ _;
  match goal with
  | [r := div.modn ?x (S ?y) |- _ ] => 
    let x_t := fresh "_dividend_" in 
    let divP := fresh "_divP_" in 
    set q := div.divn x (S y);
    set x_t := x; 
    move: (div.divn_eq x (S y)); rewrite - {1} [x] /x_t => divP;
    rewrite ? divP /x_t ; clear x_t divP;
    (have : lt r (S y) by apply/ssrnat.ltP/div.ltn_pmod);
    move: (div.divn_eq x (S y)); rewrite - ? /r - ? /q /=;
    move: r q; intros ? ?;
    rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=
  | [r := div.modn ?x ?y |- _ ] => 
    let y_t := fresh "divisor_" in
    let Ey := fresh "_divisorE_" in
    set y_t := y in r *;
    (have: y_t = y by []);
    (have: r = div.modn x y_t by []);
    move: y_t r; case; 
    [ move => r;
      rewrite ? AutoNatTheory.Q13 ? AutoNatTheory.Q14 => ->; clear r
    | let Er := fresh "_remainderE_" in
      let x_t := fresh "_dividend_" in
      let divP := fresh "_divP_" in
      move => y_t r /[swap] Ey Er;
      set q := div.divn x (S y_t);
      set x_t := x;
      move: (div.divn_eq x (S y_t)); rewrite - {1} [x] /x_t => divP;
      rewrite ? divP /x_t; clear x_t divP;
      (have : lt (div.modn x (S y_t)) (S y_t)
        by apply/ssrnat.ltP/div.ltn_pmod);
      move: (div.divn_eq x (S y_t)); rewrite - ? Er - ? /q;
      move: q Ey; clear Er; intros ?;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=
    ]
  end.

(* deal with fintype.bump, by case analysis *)
Ltac elim_bump :=
  let b := fresh "bump" in
  set b := fintype.bump _ _;
  match goal with
  | [b := fintype.bump ?h ?i |- _ ] => 
    let E := fresh "bump_case" in
    case: (ssrnat.ltnP i h) => E;
    [ (have -> : b = i by rewrite /b /fintype.bump leqNgt E);
      move: E => /ssrnat.ltP; clear b 
    | (have -> : b = S i by rewrite /b /fintype.bump E);
      move: E => /ssrnat.leP; clear b
    ]
  end.

Ltac move2 := repeat match goal with
  | [ |- is_true true ] => apply is_true_true  (* trivial *)
  | [ |- is_true false -> _ ] => move=>/AutoNatTheory.Q0 [] (* trivial *)
  | [ |- forall n : 'I_0, _ ] => let n := fresh "n" in  (* trivial *)
                                 move=>n; apply (AutoNatTheory.Q01 n)
  | [ |- forall (_ : lt _ 0), _ ] => let H := fresh "Hcontra" in  (* trivial *)
                                 move=>H; apply (@AutoNatTheory.Q02 _ H)
  | [ |- forall (_ : le 0 _), _ ] => move=> _  (* trivial *)
  | [ |- is_true true -> _ ] => move=> _  (* trivial *)
  | [ |- forall _ : ordinal _, _ ] => 
      (* idtac "case ord"; *)
      let x := fresh "n" in
      let h := fresh "H" in
      case => x ; rewrite ? (AutoNatTheory.R4,AutoNatTheory.Qord) /= => h;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=;
      move: h {+} h => /ssrnat.ltP;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=;
      (try move => + _ ); (try do ? elim_odd); (try do ? elim_div);
      (try do ? elim_mod); (try do ? elim_bump)
  | [ |- forall _ : nat, _ ] => 
      (* idtac "move nat"; *)
      let x := fresh "n" in 
      move => x /=; rewrite ? (AutoNatTheory.R4,AutoNatTheory.Qord) /=; 
      (try do ? elim_odd); (try do ? elim_div); (try do ? elim_mod);
      (try do ? elim_bump)
  | [ |- is_true (leq (S _) _) -> _ ] => let x := fresh "H" in 
      move => /= /ssrnat.ltP x;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /= in x
  | [ |- is_true (leq _ _) -> _ ] => let x := fresh "H" in 
      move => /= /ssrnat.leP x;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /= in x
  | [ |- is_true (_ == _) -> _ ] => let x := fresh "H" in 
      move => /= /eqP x;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /= in x
  | [ |- is_true (_ != _) -> _ ] => let x := fresh "H" in 
      move => /= /eqP x;
      rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /= in x
  | [ |- _ -> _ ] => 
      (* idtac "move prop"; *)
      let x := fresh "H" in
      move => /= x;
      rewrite /= ? (AutoNatTheory.R4, AutoNatTheory.Qord) /= 
                 ? (AutoNatTheory.Qm, AutoNatTheory.Qnat) in x
  | [ |- forall _, _ ] => 
      (* idtac "move var"; *)
      let x := fresh "x" in
      move => /= x /=; rewrite ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=; 
      (try do ? elim_odd); (try do ? elim_div);
      (try do ? elim_mod); (try do ? elim_bump)
  | [ |- _ ] => rewrite /= ? (AutoNatTheory.R4, AutoNatTheory.Qord) /=
                           ? (AutoNatTheory.Qm, AutoNatTheory.Qnat)
end.

Ltac mc_nat_convert :=
  move_all; move_ord; move_all; move2; move_all;
  rewrite ?AutoNatTheory.Rm.
Ltac mc_nat :=
  move_all; move_ord; move_all; move2; move_all;
  rewrite ?AutoNatTheory.Rm; Lia.nia.

End AutoNat.

Ltac mc_nat_convert := AutoNat.mc_nat_convert.
Ltac mc_nat := AutoNat.mc_nat.

Section test.
Context (k : nat).

Goal forall m, half m = uphalf m \/ (half m).+1 = uphalf m.
time mc_nat.
Qed.

Goal forall m, (uphalf m + half m = m)%N.
Proof. mc_nat. Qed.

Definition L1 {n} {i : 'I_n} (j : 'I_i) := (widen_ord (ltnW (ltn_ord i)) j).
Definition L2 {n} {i : 'I_n} (j : 'I_(rev_ord i)) :=
  (rev_ord (widen_ord (ltnW (ltn_ord (rev_ord i))) (rev_ord j))).

Goal forall a b c, 
  a <= b -> a == b -> b < c -> a <= c.
time mc_nat.
Qed.

Goal forall (n : nat) (a : 'I_n./2) (b : 'I_n./2) (c : 'I_a), 
  a <= b -> a == b -> b < c -> a <= c.
time mc_nat.
Qed.

Goal forall m n, m < n./2 + 1 -> m <> (n+2) - (m+1).
time mc_nat.
Qed.

Goal forall (n : nat) (m : 'I_(n./2+1)),
  m != (n.+2) - (m.+1) :> nat.
time mc_nat.
Qed.

Goal forall m n, m < n./2 + 1 -> (n./2 + 1) - m.+1 <> (n+2) - (m+1).
time mc_nat.
Qed.

Goal forall (n : nat) (m : 'I_(n./2+1)),
  rev_ord m != (n+2) - (m+1) :> nat.
time mc_nat.
Qed.

Goal forall m n, m < n./2 + 1 -> m <> (n+2) - (m+1).
time mc_nat.
Qed.

Goal forall a b q : nat, b <> 0 -> b * q <= a <-> q <= a %/ b.
time mc_nat.
Qed.

Goal forall a b q : nat, 0 < b -> b * q <= a <-> q <= a %/ b.
time mc_nat.
Qed.

Goal forall a b q : nat, 0 < b -> b * q <= a <-> q <= a %/ b.
time mc_nat.
Qed.

Goal forall n m, m < n./2 + 1 -> m <> (n+2) - (m+1).
time mc_nat.
Qed.

Goal forall n m, min n m <= n.
time mc_nat.
Qed.

Goal forall n m, max n m >= n.
time mc_nat.
Qed.

Goal forall n (m : 'I_n) (k : 'I_m.+1), (m * k + m <> n * k + n).
time mc_nat.
Qed.

Goal forall n (i : 'I_n) (j1 : 'I_i) (j2 : 'I_(rev_ord i)),
   (L1 j1) != (L2 (rev_ord j2)).
time mc_nat.
Qed.

Goal forall n (i : 'I_n), lift (lift ord0 i) i != lift (lift ord_max i) i.
time mc_nat.
Qed.

End test.
