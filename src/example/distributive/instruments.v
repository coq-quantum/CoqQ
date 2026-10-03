(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.distributive Require Import language operational scheduler local_actions.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedInstruments.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition atom_index (a : atom) : choiceType :=
  match a with
  | ARandom t _ _ => CL.value t
  | AMeasure t _ _ _ _ => eval_qtype t
  | _ => Choice.clone unit _
  end.

Fixpoint local_index s : choiceType :=
  match s with
  | Atomic a => atom_index a
  | Sequence s _ => local_index s
  | _ => Choice.clone unit _
  end.

Definition atom_control (a : atom) m : atom_index a -> (statement * option cmem) :=
  match a as a' return atom_index a' -> (statement * option cmem) with
  | AAbort => fun _ => (Finished,None)
  | AAssign _ x e => fun _ => (Finished,Some (m.[x <- eval e m])%M)
  | ARandom _ x _ => fun i => (Finished,Some (m.[x <- i])%M)
  | AMeasure _ _ x _ _ => fun i => (Finished,Some (m.[x <- i])%M)
  | _ => fun _ => (Finished,Some m)
  end.

Fixpoint local_control s m : local_index s -> (statement * option cmem) :=
  match s as s' return local_index s' -> (statement * option cmem) with
  | Finished => fun _ => (Finished,Some m)
  | Atomic a => @atom_control a m
  | Sequence s t => fun i => (append (@local_control s m i).1 t, (@local_control s m i).2)
  | Alternative n g b => fun _ =>
      if [pick j | eval (g j) m] is Some j then (b j,Some m) else (Finished,None)
  | Repetition n g b => fun _ =>
      if [pick j | eval (g j) m] is Some j
      then (Sequence (b j) (Repetition g b),Some m) else (Finished,Some m)
  end.

Definition atom_map (a : atom) m : atom_index a -> 'SO(Hq) :=
  match a as a' return atom_index a' -> 'SO(Hq) with
  | ARandom _ _ p => fun i => CL.probability_mass p m i *: \:1
  | AInitial _ q phi => fun _ => liftfso (initialso (tv2v q (eval phi m)))
  | AUnitary _ q U => fun _ => liftfso (formso (tf2f q q (eval U m)))
  | AMeasure _ _ _ q M => fun i => CL.measurement_branches q M m i
  | _ => fun _ => \:1
  end.

Fixpoint local_map s m : local_index s -> 'SO(Hq) :=
  match s as s' return local_index s' -> 'SO(Hq) with
  | Atomic a => @atom_map a m
  | Sequence s _ => @local_map s m
  | _ => fun _ => \:1
  end.

Lemma atom_map_cp a m i : @atom_map a m i \is cpmap.
Proof.
case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i /=.
- exact: is_cpmap.
- exact: is_cpmap.
- exact: is_cpmap.
- rewrite -geso0_cpE; apply: scalev_ge0.
  + exact: ge0_mu.
  + exact: cp_geso0.
- exact: is_cpmap.
- exact: is_cpmap.
- exact: is_cpmap.
Qed.

Lemma local_map_cp s m i : @local_map s m i \is cpmap.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /=.
- exact: is_cpmap.
- exact: atom_map_cp.
- exact: IH.
- exact: is_cpmap.
- exact: is_cpmap.
Qed.

Definition local_cp s m i := CPMap_Build (@local_map_cp s m i).

Lemma atom_map_external a m i S (F : 'SO_S) :
  [disjoint atom_quantum a & S] ->
  @atom_map a m i :o liftfso F = liftfso F :o @atom_map a m i.
Proof.
case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- by rewrite comp_soZl comp_soZr comp_so1l comp_so1r.
- exact: liftfso_compC.
- exact: liftfso_compC.
- rewrite CL.measurement_branchE; exact: liftfso_compC.
Qed.

Lemma local_map_external s m i S (F : 'SO_S) :
  [disjoint statement_quantum s & S] ->
  @local_map s m i :o liftfso F = liftfso F :o @local_map s m i.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- exact: atom_map_external.
- apply: IH; exact: fintype.disjointWl (finset.subsetUl _ _) Hdis.
Qed.


Lemma normalized_channel (E : 'QC(Hq)) rho : rho \is den1lf ->
  normalized_output E rho = E rho.
Proof.
move=>Hr; rewrite /normalized_output qc_trlfE (den1lf_trlf Hr) ltr01 invr1 scale1r.
by [].
Qed.

Lemma normalized_scalar p rho : rho \is den1lf ->
  normalized_output (p *: (\:1 : 'SO(Hq))) rho = rho.
Proof.
move=>Hr; rewrite /normalized_output !soE linearZ /= (den1lf_trlf Hr) mulr1.
case: ifP=>Hp; last by [].
by rewrite scalerA mulVf ?gt_eqF // scale1r.
Qed.

Definition local_family s m rho : family local_configuration :=
  @Family _ (local_index s) (fun i => \Tr (@local_map s m i rho))
    (fun i => local_config (@local_control s m i).1 (@local_control s m i).2
      (normalized_output (@local_map s m i) rho)).

Lemma atom_realization a m rho : rho \is den1lf ->
  atom_successor a m rho = local_family (Atomic a) m rho.
Proof.
move=>Hr; case: a=>[| |t x e|t x p|t q phi|t q U|t u x q M];
  rewrite /atom_successor /local_family /=.
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- congr (@Family _ _ _ _); apply/funext=>i.
  + by rewrite !soE linearZ /= (den1lf_trlf Hr) mulr1.
  + by rewrite normalized_scalar.
- by rewrite normalized_channel // qc_trlfE (den1lf_trlf Hr).
- by rewrite normalized_channel // qc_trlfE (den1lf_trlf Hr).
- by rewrite /measurement_branch /normalized_output.
Qed.

Lemma local_realization s m rho : rho \is den1lf ->
  local_successor s m rho = local_family s m rho.
Proof.
move=>Hr; elim: s=>[|a|s IH t IHt|n g b IH|n g b IH] /=.
- by rewrite /local_family /= normalized_channel // !soE (den1lf_trlf Hr).
- exact: atom_realization.
- by rewrite IH /local_family /fmap /append_configuration /local_config.
- rewrite /local_family /=; case: pickP=>[i Hi|Hnone];
    by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- rewrite /local_family /=; case: pickP=>[i Hi|Hnone];
    by rewrite normalized_channel // !soE (den1lf_trlf Hr).
Qed.

End DistributedInstruments.
