From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.

Require Import mcextra mcaextra notation convex.
Require Import hermitian quantum inhabited qreg qtype.
From quantum.example.qlaws Require Import basic_def circuit nondeterministic.

Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Section Example.
Import NonDeterministicAuto.Exports.

Section Example_1_1.
(* assume we have three quantum variables q, q1 and q2 *)
Context (q q1 q2 : qvart Bool).
(* assume these variables are distinct *)
Context (dis : qvar_dis [:: (q : qvar); (q1 : qvar); (q2 : qvar)]).

Definition QEC := <{[  
  [q1] := '0 ;; 
  [q2] := '0 ;; 
  [cir [q] → ([q1] *= ''X)] ;; 
  [cir [q] → ([q2] *= ''X)] ;;
  ( skip ⊔ [cir [q] *= ''X] ⊔ [cir [q1] *= ''X] ⊔ [cir [q2] *= ''X] ) ;;
  [cir [q] → ([q2] *= ''X)] ;; 
  [cir [q] → ([q1] *= ''X)] ;; 
  [q2] ▷ ([q1] ▷ [cir [q] *= ''X])
]}>.

Lemma QEC_simple :
  QEC =c <{[ ([q1] := '0 ;; [q2] := '0) ⊔ ([q1] := '1 ;; [q2] := '1) ⊔
             ([q1] := '1 ;; [q2] := '0) ⊔ ([q1] := '0 ;; [q2] := '1) ]}>.
Proof.
(* associativity of nchoice ; proposition 7.1 (2) *)
rewrite -!nchoiceA /QEC.
(* left/right distributivity of nchoice w.r.t. sequence ; proposition 7.1 (5) *)
rewrite !(nchoice_seqc_distrl , nchoice_seqc_distrr).
(* equivalence of each fragment *)
do ! apply eq_nchoice.
- (* eliminate skip ; proposition 5.4 (1) *)
  rewrite skipxI.
  (* rearrange to the composition of circuits *)
  rewrite -!seqc_circuitA.
  (* composition of quantum if ; proposition 4.2 (7) *)
  rewrite 2!qif_sequB.
  (* associativity of circuit composition ; proposition 4.2 (6) *)
  rewrite -!sequA.
  (* composition of unitary transformation ; proposition 4.2 (3) *)
  rewrite unit_sequ/=.
  (* identify that [q2] *= ''X \o ''X =u uskip ; proposition 4.2 (2) *)
  rewrite [in X in qcond2_ _ _ _ (sequ_ X _)]uskip_eqP/=.
    (* since ''X \o ''X = \1 (i.e., identity) *)
    by rewrite ?PauliX_id.
  (* composition of quantum if ; proposition 4.2 (7) *)
  rewrite qif_sequB.
  (* eliminate uskip ; proposition 4.2 (1) *)
  rewrite !uskipIx.
  (* composition of unitary transformation ; proposition 4.2 (3) *)
  rewrite unit_sequ/=.
  (* identify that [q2] *= ''X \o ''X =u uskip ; proposition 4.2 (2) *)
  rewrite uskip_eqP/= ?PauliX_id//.
  (* qif is idempotent ; proposition 4.1 (3) *)
  rewrite qif_idemB.
  (* circuit uskip is the same as program skip *)
  rewrite uskip_skip.
  (* eliminate skip ; proposition 5.4 (1) *)
  rewrite skipxI.
  (* associativity of program composition ; proposition 5.4 (3) *)
  rewrite !seqcA.
  (* if elimination ; proposition 5.1 (4) *)
  rewrite init_ifFK/=.
    (* different onb basis are orthogonal *)
    by rewrite ?onb_dot.
  (* eliminate skip ; proposition 5.4 (1) *)
  by rewrite skipxI.
- (* rearrange to the composition of circuits *)
  rewrite -!seqc_circuitA.
  (* composition of quantum if ; proposition 4.2 (7) *)
  rewrite qif_sequB.
  (* associativity of circuit composition ; proposition 4.2 (6) *)
  rewrite -!sequA.
  (* composition of quantum if ; proposition 4.2 (7) *)
  rewrite qif_sequB.
  (* symmetry of quantum choice; proposition 4.3 (1) *)
  rewrite -qchoice_sym.
  (* associativity of circuit composition ; proposition 4.2 (6) *)
  rewrite sequA.
  (* composition of quantum if ; proposition 4.2 (7) *)
  rewrite qif_sequB.
  (* associativity of circuit composition ; proposition 4.2 (6) *)
  rewrite -!sequA.
  (* eliminate uskip ; proposition 4.2 (1) *)
  rewrite !uskipIx !uskipxI.
  (* commutative of disjoint circuits; proposition 4.2 (4) *)
  rewrite sequC.
  (* qif is idempotent ; proposition 4.1 (3) *)
  rewrite qif_idemB.
  (* commutative of disjoint circuits; proposition 4.2 (4) *)
  rewrite sequC.
  (* associativity of circuit composition ; proposition 4.2 (6) *)
  rewrite sequA.
  (* rearrange of the composition of circuits *)
  rewrite seqc_circuitA. 
  (* associativity of program composition ; proposition 5.4 (3) *)
  rewrite seqcA [in X in seqc_ X _]seqcA.
  (* unitary elimination ; proposition 5.1 (2) *)
  rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/=.
    (* identify that X |0> = |1> *)
    by rewrite PauliX_cb.
  (* rearrange the program by associativity (proposition 5.4 (3))
     and commutativity of disjoint programs (proposition 5.4 (2)) *)
  rewrite seqcA -[in X in seqc_ _ X]seqcA.
  rewrite [in X in seqc_ _ (seqc_ X _)]seqcC seqcA.
  (* if elimination ; proposition 5.1 (4) *)
  rewrite init_ifTK/=.
  (* associativity of program composition ; proposition 5.4 (3) *)
  rewrite -!seqcA.
  (* rearrange of the composition of circuits *)
  rewrite seqc_circuitA.
  (* unitary elimination ; proposition 5.1 (2) *)
  rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/=.
    (* identify that X |0> = |1> *)
    by rewrite PauliX_cb.
  (* rearrange the program by associativity (proposition 5.4 (3))
     and commutativity of disjoint programs (proposition 5.4 (2)) *)
  rewrite [in X in seqc_ X _]seqcA seqcC seqcA.
  (* if elimination ; proposition 5.1 (4) *)
  rewrite init_ifTK/=.
  (* rearrange the program by associativity (proposition 5.4 (3))
     and commutativity of disjoint programs (proposition 5.4 (2)) *)
  rewrite seqcC seqcA -[in X in seqc_ _ X]seqcA.
  rewrite [in X in seqc_ _ X]seqcC -seqc_circuitA.
  (* composition of unitary transformation ; proposition 4.2 (3) *)
  rewrite unit_sequ/=.
  (* identify that [q] *= ''X \o ''X =u uskip ; proposition 4.2 (2) *)
  rewrite uskip_eqP/= ?PauliX_id//.
  (* circuit uskip is the same as program skip *)
  rewrite uskip_skip.
  (* eliminate skip ; proposition 5.4 (1) *)
  rewrite skipxI.
  (* commutativity of disjoint programs ; proposition 5.4 (2) *)
  rewrite seqcC.
  by [].
- (* we can similarly prove the rest two subgoals *)
  rewrite -{2}(@qif_idemB <{q}> t2tv <{[[q1] *= ''X]}>).
  rewrite -!seqc_circuitA !qif_sequB !uskipxI !uskipIx sequC.
  rewrite -[X in sequ_ _ (sequ_ _ X)]sequA [in X in sequ_ _ (sequ_ _ X)]unit_sequ/=.
  rewrite [in X in sequ_ _ (sequ_ _ X)]uskip_eqP/= ?PauliX_id// uskipIx.
  rewrite [in X in sequ_ _ X]unit_sequ/= [in X in sequ_ _ X]uskip_eqP/= ?PauliX_id// uskipxI.
  rewrite qif_idemB seqcC [X in seqc_ X _]seqcA.
  rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
  by rewrite seqcC seqcA init_ifFK/= ?onb_dot// skipxI.
- rewrite -{2}(@qif_idemB <{q}> t2tv <{[[q2] *= ''X]}>).
  rewrite -!seqc_circuitA !qif_sequB !uskipxI !uskipIx sequC.
  rewrite -[X in sequ_ _ X]sequA unit_sequ/=.
  rewrite [in X in sequ_ _ (sequ_ X _)]uskip_eqP/= ?PauliX_id// uskipIx.
  rewrite -sequA unit_sequ/= [in X in (sequ_ X _)]uskip_eqP/= ?PauliX_id// uskipIx.
  rewrite qif_idemB [X in seqc_ X _]seqcA.
  rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
  by rewrite seqcA init_ifTK/= -seqcA seqcC seqcA init_ifFK ?onb_dot// skipxI seqcC.
Qed.

(* nested proofs *)
(* Lemma QEC_simple :
  QEC =c <{[
    ([q1] := '0 ;; [q2] := '0) ⊔
    ([q1] := '1 ;; [q2] := '1) ⊔
    ([q1] := '1 ;; [q2] := '0) ⊔
    ([q1] := '0 ;; [q2] := '1)
  ]}>.
Proof.
rewrite -!nchoiceA.
rewrite /QEC !(nchoice_seqc_distrl , nchoice_seqc_distrr).
do ! apply eq_nchoice.
- rewrite skipxI -!seqc_circuitA 2!qif_sequB -!sequA unit_sequ/=.
  rewrite [in X in qcond2_ _ _ _ (sequ_ X _)]uskip_eqP/= ?PauliX_id//.
  rewrite qif_sequB !uskipIx unit_sequ/= uskip_eqP/= ?PauliX_id//.
  rewrite qif_idemB uskip_skip skipxI !seqcA init_ifFK/= ?onb_dot//=.
  by rewrite skipxI.
- rewrite -!seqc_circuitA qif_sequB -!sequA qif_sequB -qchoice_sym.
  rewrite sequA qif_sequB -!sequA !uskipIx !uskipxI sequC qif_idemB.
  rewrite sequC sequA seqc_circuitA seqcA [in X in seqc_ X _]seqcA 
    (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
  rewrite seqcA -[in X in seqc_ _ X]seqcA [in X in seqc_ _ (seqc_ X _)]seqcC.
  rewrite seqcA init_ifTK/= -!seqcA seqc_circuitA .
  rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
  rewrite [in X in seqc_ X _]seqcA seqcC seqcA init_ifTK/= seqcC.
  rewrite seqcA -[in X in seqc_ _ X]seqcA [in X in seqc_ _ X]seqcC -seqc_circuitA.
  by rewrite unit_sequ/= uskip_eqP/= ?PauliX_id// uskip_skip skipxI seqcC.
- rewrite -{2}(@qif_idemB <{q}> t2tv <{[[q1] *= ''X]}>).
  rewrite -!seqc_circuitA !qif_sequB !uskipxI !uskipIx sequC.
  rewrite -[X in sequ_ _ (sequ_ _ X)]sequA [in X in sequ_ _ (sequ_ _ X)]unit_sequ/=.
  rewrite [in X in sequ_ _ (sequ_ _ X)]uskip_eqP/= ?PauliX_id// uskipIx.
  rewrite [in X in sequ_ _ X]unit_sequ/= [in X in sequ_ _ X]uskip_eqP/= ?PauliX_id// uskipxI.
  rewrite qif_idemB seqcC [X in seqc_ X _]seqcA.
  rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
  by rewrite seqcC seqcA init_ifFK/= ?onb_dot// skipxI.
- rewrite -{2}(@qif_idemB <{q}> t2tv <{[[q2] *= ''X]}>).
  rewrite -!seqc_circuitA !qif_sequB !uskipxI !uskipIx sequC.
  rewrite -[X in sequ_ _ X]sequA unit_sequ/=.
  rewrite [in X in sequ_ _ (sequ_ X _)]uskip_eqP/= ?PauliX_id// uskipIx.
  rewrite -sequA unit_sequ/= [in X in (sequ_ X _)]uskip_eqP/= ?PauliX_id// uskipIx.
  rewrite qif_idemB [X in seqc_ X _]seqcA.
  rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
  by rewrite seqcA init_ifTK/= -seqcA seqcC seqcA init_ifFK ?onb_dot// skipxI seqcC.
Qed. *)

End Example_1_1.

End Example.
