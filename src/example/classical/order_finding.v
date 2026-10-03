(* Literal Section 7.4 source, with explicit partial postprocessing result.
   See ORDER-FINDING-NOTES.md; no disputed success estimate is assumed. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import language deterministic algorithm_semantics
  phase_program fourier shor_arithmetic modular_unitary.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalOrderFinding.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmSemantics
  ClassicalPhaseProgram ClassicalModularUnitary.
Local Notation Hq := 'H[msys]_finset.setT.
Section Program.
Variables (N L t : nat).
Hypothesis modulus_nontrivial : (1 < N)%N.
Hypothesis register_capacity : (N <= 2 ^ L)%N.
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).

Lemma modulus_positive : (0 < N)%N.
Proof. exact: ltnW modulus_nontrivial. Qed.

Definition total_modular_unitary b : 'FU('Hs(L.-tuple bool)) :=
  match asboolP (coprime b N) with
  | ReflectT H => @modular_unitary b N H modulus_positive L register_capacity
  | ReflectF _ => (\1 : 'FU('Hs(L.-tuple bool)))
  end.

Lemma total_modular_unitaryE b (Hb : coprime b N) :
  total_modular_unitary b = @modular_unitary b N Hb modulus_positive L register_capacity.
Proof.
rewrite /total_modular_unitary; case: asboolP=>[H|H]; last by exfalso; apply: H.
by rewrite (eq_irrelevance H Hb).
Qed.

Definition one_bits := @residue_bits N modulus_positive L register_capacity 1.
Definition one_state : 'NS('Hs(L.-tuple bool)) := ''one_bits.
Definition one_preparation : 'FU('Hs(L.-tuple bool)) :=
  VUnitary (zero_state (QArray L QBool)) one_state.

Lemma one_bits_value : (bseq2ord one_bits : nat) = 1%N.
Proof. exact: residue_one_value modulus_nontrivial. Qed.

Lemma one_preparationE :
  one_preparation (zero_state (QArray L QBool) : 'Ht (QArray L QBool)) =
    (one_state : 'Hs(L.-tuple bool)).
Proof. exact: VUnitaryE. Qed.

Definition all_hadamards : 'FU('Hs(t.-tuple bool)) :=
  [unitary of tentf_tuple (fun _ : 'I_t => (Hadamard : 'FU('Hs bool)))].

Definition controlled_powers b : 'FU('Ht (QPair (QArray t QBool) (QArray L QBool))) :=
  [unitary of Multiplexer (fun j : t.-tuple bool =>
    [unitary of (total_modular_unitary b)%:VF ^+ (bseq2ord j)])].

Lemma controlled_powersE b j v :
  controlled_powers b (''j ⊗t v) =
  ''j ⊗t ((total_modular_unitary b)%:VF ^+ (bseq2ord j)) v.
Proof. exact: MultiplexerEt. Qed.

Variable x : expression nat.

Definition prefix :=
  Sequence (Initialize (control_register qr) (EConst (zero_state (QArray t QBool))))
  (Sequence (Unitary (control_register qr) (EConst all_hadamards))
  (Sequence (Initialize (target_register qr) (EConst (zero_state (QArray L QBool))))
  (Sequence (Unitary (target_register qr) (EConst one_preparation))
  (Sequence (Unitary qr (EApp (EConst controlled_powers) x))
    (Unitary (control_register qr) (EConst [unitary of (ClassicalFourier.tuple_fourier t)^A])))))).

Definition prefix_action s : 'SO(Hq) :=
  ((((liftfso (formso (tf2f (control_register qr) (control_register qr)
       (ClassicalFourier.tuple_fourier t)^A)) :o
     liftfso (formso (tf2f qr qr (controlled_powers (eval x s))))) :o
     liftfso (formso (tf2f (target_register qr) (target_register qr) one_preparation))) :o
     liftfso (initialso (tv2v (target_register qr) (zero_state (QArray L QBool))))) :o
     liftfso (formso (tf2f (control_register qr) (control_register qr) all_hadamards))) :o
     liftfso (initialso (tv2v (control_register qr) (zero_state (QArray t QBool)))).

Lemma prefix_execution s : execution prefix s s (prefix_action s).
Proof.
exact: (RunSequence (RunInitialize _ _ s)
  (RunSequence (RunUnitary _ _ s)
  (RunSequence (RunInitialize _ _ s)
  (RunSequence (RunUnitary _ _ s)
  (RunSequence (RunUnitary _ _ s) (RunUnitary _ _ s)))))).
Qed.

Lemma prefix_denote s m : denote prefix s m = point s (prefix_action s) m.
Proof. apply: execution_denote; exact: prefix_execution. Qed.

Lemma prefix_channel s : prefix_action s \is cptp.
Proof. exact: execution_channel (prefix_execution s). Qed.

Definition printed_result (bs : t.-tuple bool) :=
  ClassicalShorArithmetic.printed_postprocess (bseq2ord bs) (2 ^ t)%N.

Definition order_finding
  (measured : variable (QType (QArray t QBool))) (result : variable (COption CNat)) :=
  Sequence prefix
  (Sequence (Measure measured (control_register qr)
    (EConst [QM of @tmeas (eval_qtype (QArray t QBool))]))
    (Assign result (EApp (EConst printed_result) (EVar measured)))).

End Program.
End ClassicalOrderFinding.
