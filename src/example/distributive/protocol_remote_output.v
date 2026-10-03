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

From quantum Require Import qtype.
From quantum.example.distributive Require Import protocol_quantum protocol_state protocol_remote_local.



Module DistributedProtocolRemoteOutput.
Import DistributedProtocolQuantum DistributedProtocolState DistributedProtocolRemoteLocal.

Lemma remote_output_on_data v x z :
  remote_output v \o remote_embed x z =
    remote_embed x z \o [> CNOT v; CNOT v <].
Proof.
apply/lfunP=>u; rewrite [LHS]comp_lfunE /remote_output sum_lfunE
  (bigD1 (x,z)) //= big1.
- move=>[y w] /negPf H.
  rewrite outpE /remote_states remote_embed_dot.
  move: H; rewrite xpair_eqE=>->.
  by rewrite mul0r scale0r.
- by rewrite /remote_states outpE remote_embed_dot !eqxx mul1r addr0
    comp_lfunE outpE linearZ.
Qed.

End DistributedProtocolRemoteOutput.
