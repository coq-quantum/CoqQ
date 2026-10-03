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
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.distributive Require Import language operational.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedScheduler.
Import DistributedLanguage DistributedOperational.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma matches_channel a b effect : matches a b effect -> channel a = channel b.
Proof. by case. Qed.

Lemma process_channel p j : channel (process_io p j) \in process_channels p.
Proof. apply/imfsetP; by exists j. Qed.

Definition rendezvous n (p : 'I_n -> process) (m : cmem) (i k : 'I_n) :=
  i != k /\ exists j l effect,
    eval (process_guard (p i) j) m /\
    eval (process_guard (p k) l) m /\
    matches (process_io (p i) j) (process_io (p k) l) effect.

Lemma rendezvous_symmetric n (p : 'I_n -> process) m i k :
  rendezvous p m i k -> rendezvous p m k i.
Proof.
move=>[ne [j [l [effect [Hi [Hk Hmatch]]]]]].
split; first by rewrite eq_sym.
exists l, j, effect; split=>//; split=>//; exact: matches_symmetric.
Qed.

(* A process with one enabled guarded branch cannot rendezvous with two
   different peers: that would place its enabled channel in three processes. *)
Lemma rendezvous_partner_unique (P : program) m i j k :
  rendezvous (processes P) m i j ->
  rendezvous (processes P) m i k -> j = k.
Proof.
move=>[Hij [a [b [effect [Ha [Hb Hab]]]]]]
       [Hik [a' [c [effect' [Ha' [Hc Hac]]]]]].
have Eaa : a = a' := (proj1 (proj2 (@processes_wf P i))) m a a' Ha Ha'.
subst a'.
case Ejk : (j == k); first by apply/eqP.
exfalso; have Hjk : j != k by rewrite Ejk.
have D := @processes_point_to_point P i j k Hij Hik Hjk.
have Ci := @process_channel (processes P i) a.
have Cj : channel (process_io (processes P i) a) \in process_channels (processes P j).
  by rewrite (matches_channel Hab); exact: process_channel.
have Ck : channel (process_io (processes P i) a) \in process_channels (processes P k).
  by rewrite (matches_channel Hac); exact: process_channel.
move/fdisjointP: D=>/(_ _ Ci); by rewrite in_fsetI Cj Ck.
Qed.

Local Close Scope fset_scope.

Definition local_enabled n (p : 'I_n -> process) pc m rho i :=
  (exists s mu, pc i = Executing s /\
     local_step (local_config s (Some m) rho) mu) \/
  (pc i = Waiting /\ [forall j, ~~ eval (process_guard (p i) j) m]).
Definition pair_enabled n (p : 'I_n -> process) pc m i k :=
  pc i = Waiting /\ pc k = Waiting /\ rendezvous p m i k.

Lemma local_pair_exclusive n (p : 'I_n -> process) pc m rho i k :
  local_enabled p pc m rho i -> ~ pair_enabled p pc m i k.
Proof.
move=>[[s [mu [Hpc Hstep]]]|[Hpc /forallP Hnone]] [Hi [Hk [ne [j [l [e [Hj [Hl Hmatch]]]]]]]].
- by rewrite Hpc in Hi.
- by move: (Hnone j); rewrite Hj.
Qed.

Inductive enabled_label n (p : 'I_n -> process) pc m rho : {set 'I_n} -> Prop :=
| EnabledLocal i : local_enabled p pc m rho i -> enabled_label p pc m rho [set i]
| EnabledPair i k : pair_enabled p pc m i k -> enabled_label p pc m rho [set i; k].


Lemma global_step_has_label n (p : 'I_n -> process) c mu : global_step p c mu ->
  exists pc m rho A, c = global_config pc (Some m) rho /\ enabled_label p pc m rho A.
Proof.
move=>d; case: d=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch].
- exists pc, m, rho, [set i]; split=>//; apply: EnabledLocal.
  left; by exists s, nu.
- exists pc, m, rho, [set i]; split=>//; apply: EnabledLocal.
  by right.
- exists pc, m, rho, [set i; k]; split=>//; apply: EnabledPair.
  split=>//; split=>//; split.
    by apply/negP=>/eqP E; move: Hik; rewrite E ltnn.
  by exists j, l, (AAssign x e); repeat split.
Qed.

Lemma enabled_labels_disjoint_or_equal (P : program) pc m rho A B :
  enabled_label (processes P) pc m rho A ->
  enabled_label (processes P) pc m rho B ->
  A = B \/ [disjoint A & B]%SET.
Proof.
move=>HA HB; inversion HA; subst A; inversion HB; subst B.
- case E : (i == i0).
  + by left; move/eqP: E=>->.
  + right; apply/disjointP=>z; rewrite !inE=>/eqP->.
    by rewrite E.
- right; apply/disjointP=>z; rewrite !inE=>/eqP->.
  apply/negP=>/orP[/eqP E|/eqP E]; subst i.
  + exact: (local_pair_exclusive H H0).
  + move: H0=>[Hi [Hk HR]].
    have HP : pair_enabled (processes P) pc m k i0.
      split; first exact Hk; split; first exact Hi.
      exact: rendezvous_symmetric HR.
    exact: (local_pair_exclusive H HP).
- right; rewrite disjoint_sym; apply/disjointP=>z; rewrite !inE=>/eqP->.
  apply/negP=>/orP[/eqP E|/eqP E]; subst i0.
  + exact: (local_pair_exclusive H0 H).
  + move: H=>[Hi [Hk HR]].
    have HP : pair_enabled (processes P) pc m k i.
      split; first exact Hk; split; first exact Hi.
      exact: rendezvous_symmetric HR.
    exact: (local_pair_exclusive H0 HP).
- move: H H0=>[Hi [Hk HR]] [Hi0 [Hk0 HR0]].
  case Eii : (i == i0).
    move/eqP: Eii=>Ei; subst i0.
    have Ek := rendezvous_partner_unique HR HR0; subst k0; by left.
  case Eik : (i == k0).
    move/eqP: Eik=>Ei; subst k0.
    have Ek := rendezvous_partner_unique HR (rendezvous_symmetric HR0).
    subst i0; left; apply/setP=>z; by rewrite !inE orbC.
  case Eki : (k == i0).
    move/eqP: Eki=>Ek; subst i0.
    have Ei := rendezvous_partner_unique (rendezvous_symmetric HR) HR0.
    subst k0; left; apply/setP=>z; by rewrite !inE orbC.
  case Ekk : (k == k0).
    move/eqP: Ekk=>Ek; subst k0.
    have Ei := rendezvous_partner_unique (rendezvous_symmetric HR)
      (rendezvous_symmetric HR0).
    subst i0; by left.
  right; apply/disjointP=>z; rewrite !inE=>/orP[/eqP->|/eqP->].
  + by rewrite Eii Eik.
  + by rewrite Eki Ekk.
Qed.

Lemma replace_same n (pc : 'I_n -> control) i c : replace pc i c i = c.
Proof. by rewrite /replace eqxx. Qed.

Lemma replace_other n (pc : 'I_n -> control) i j c :
  j != i -> replace pc i c j = pc j.
Proof. by move=>/negbTE H; rewrite /replace H. Qed.

Lemma replace_commute n (pc : 'I_n -> control) i j ci cj : i != j ->
  replace (replace pc i ci) j cj = replace (replace pc j cj) i ci.
Proof.
move=>Hij; apply/funext=>k; rewrite /replace.
case Eki: (k == i); case Ekj: (k == j)=>//.
move/eqP: Eki=>Eki; subst k.
by move: Hij; rewrite Ekj.
Qed.


Definition residual_wf s := s = Finished \/ statement_wf s.

Lemma append_wf s t : residual_wf s -> statement_wf t -> statement_wf (append s t).
Proof. by case: s=>//=; rewrite /residual_wf /=; intuition discriminate. Qed.

Lemma local_step_wf c mu : local_step c mu -> statement_wf c.1.1 ->
  forall i, residual_wf (branch_value mu i).1.1.
Proof.
move=>H; induction H; cbn [local_config certain branch_value fmap];
  move=>Hwf outcome; try by left.
- right; apply: append_wf; last exact: (proj2 Hwf).
  exact: (IHlocal_step (proj1 Hwf) outcome).
- right; exact: (proj2 Hwf).
- right; split=>//; exact: (proj2 Hwf).
Qed.

Local Open Scope fset_scope.

Lemma branch_changes_subset n (b : 'I_n -> statement) i :
  statement_changes (b i) `<=` \big[fsetU/fset0]_j statement_changes (b j).
Proof. by rewrite (bigD1 i) //=; exact: fsubsetUl. Qed.

Lemma append_changes s t : statement_changes (append s t) `<=`
  statement_changes s `|` statement_changes t.
Proof. by case: s=>//=; rewrite fset0U. Qed.

Lemma local_step_changes c mu : local_step c mu -> forall i,
  statement_changes (branch_value mu i).1.1 `<=` statement_changes c.1.1.
Proof.
move=>H; induction H; cbn [local_config certain branch_value fmap];
  move=>outcome; try exact: fsub0set.
- apply: fsubset_trans (append_changes _ _ ) _.
  by rewrite fsubUset (fsubset_trans (IHlocal_step outcome) (fsubsetUl _ _))
    (fsubsetUr _ _).
- exact: branch_changes_subset.
- by rewrite /= fsubUset branch_changes_subset fsubset_refl.
Qed.


Local Close Scope fset_scope.

Definition normalized_output (E : 'SO(Hq)) rho :=
  if 0 < \Tr (E rho) then (\Tr (E rho))^-1 *: E rho else rho.

Lemma normalized_output_den1 (E : 'CP(Hq)) rho : rho \is den1lf ->
  normalized_output E rho \is den1lf.
Proof.
move=>Hr; rewrite /normalized_output; case: ifP=>Htr; last exact: Hr.
apply/den1lfP; split.
  apply: psdlfZ; first by rewrite invr_ge0; exact: ltW Htr.
  apply: cp_psdP; exact: den1lf_psd Hr.
by rewrite linearZ /= mulVf ?gt_eqF.
Qed.

Lemma weighted_normalized_output (E : 'CP(Hq)) rho : rho \is den1lf ->
  \Tr (E rho) *: normalized_output E rho = E rho.
Proof.
move=>Hr; rewrite /normalized_output; case: ifP=>Htr.
  by rewrite scalerA mulfV ?gt_eqF // scale1r.
have Hp : E rho \is psdlf by apply: cp_psdP; exact: den1lf_psd Hr.
have Hzero : \Tr (E rho) = 0.
  by move: (psdlf_trlf Hp); rewrite le_eqVlt Htr orbF eq_sym=>/eqP.
have Ez : E rho == 0 := introT (@trlf0_eq0 Hq (E rho)) (conj (psdlf_ge0 Hp) Hzero).
by rewrite Hzero scale0r (eqP Ez).
Qed.

Lemma weighted_two_normalized_outputs (E F : 'CP(Hq)) rho : rho \is den1lf ->
  (\Tr (E rho) * \Tr (F (normalized_output E rho))) *:
    normalized_output F (normalized_output E rho) = F (E rho).
Proof.
move=>Hr; rewrite -scalerA (weighted_normalized_output F (normalized_output_den1 E Hr)).
by rewrite -linearZ /= (weighted_normalized_output E Hr).
Qed.

Lemma commuting_normalized_outputs (E F : 'CP(Hq)) rho :
  rho \is den1lf -> E :o F = F :o E ->
  (\Tr (E rho) * \Tr (F (normalized_output E rho))) *:
    normalized_output F (normalized_output E rho) =
  (\Tr (F rho) * \Tr (E (normalized_output F rho))) *:
    normalized_output E (normalized_output F rho).
Proof.
by move=>Hr Hcomm; rewrite !weighted_two_normalized_outputs //;
  exact: commuting_joint_state.
Qed.

End DistributedScheduler.
