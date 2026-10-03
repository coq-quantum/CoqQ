(* Branch equations for distributed protocols; see PROTOCOLS-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From quantum Require Import hspace_extra.

Module DistributedProtocolEffect.

Lemma effect_saturated (U : chsType) (A : 'FO(U)) (v : U) :
  [< v; v >] = 1 -> [< v; A v >] = 1 -> A v = v.
Proof.
move=>Hnorm Hv.
have Hzero : [< (v : U); (cplmt A) v >] = 0.
  by rewrite /cplmt lfunE /= id_lfunE opp_lfunE dotpBr Hnorm Hv subrr.
have Hz := psdf_dot_eq0P Hzero.
move: Hz; rewrite /cplmt lfunE /= id_lfunE opp_lfunE.
by move=>/subr0_eq /esym.
Qed.

Lemma effect_contains_state (U : chsType) (A : 'FO(U)) (v : U) :
  [< v; v >] = 1 -> [< v; A v >] = 1 -> [> (v : U); v <] ⊑ (A : 'End(U)).
Proof.
move=>Hnorm Hv.
have Av := effect_saturated Hnorm Hv.
have AP : (A : 'End(U)) \o [> (v : U); v <] = [> (v : U); v <].
  by rewrite -outp_complV Av.
have PA : [> (v : U); v <] \o (A : 'End(U)) = [> (v : U); v <].
  by rewrite -(hermf_adjE A) -outp_comprV Av.
have PP : [> (v : U); v <] \o [> (v : U); v <] = [> (v : U); v <].
  by rewrite outp_comp Hnorm scale1r.
have H := gef0_formfV (cplmt [> (v : U); v <]) (obsf_ge0 A).
rewrite /cplmt adjfB adjf1 adj_outp !linearBr /= !linearBl /=
  !comp_lfun1l !comp_lfun1r AP PA PP in H.
move: H.
by rewrite subrr subr0 subv_ge0.
Qed.

End DistributedProtocolEffect.
