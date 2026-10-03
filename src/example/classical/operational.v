(* Finite terminating routes for Feng and Ying (2021), Section 4.2.
   The route representation and summation proof pattern adapt CoqQ's
   example/veri_QEC/cqwhile.v; its original file is preserved. *)
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
From quantum.example.classical Require Import language instrument.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage Summable_Reindex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Module ClassicalOperational.
Local Notation Hq := 'H[msys]_finset.setT.

Inductive route :=
  | TR_skip | TR_assign
  | TR_random {t} (v : value t)
  | TR_cond1 (r : route) | TR_cond2 (r : route)
  | TR_while0 | TR_while1 (r : route)
  | TR_seqc (r1 r2 : route)
  | TR_initial | TR_unitary
  | TR_measure {t} (v : value t).

HB.instance Definition _ := gen_eqMixin route.
HB.instance Definition _ := gen_choiceMixin route.

Fixpoint route_size (r : route) : nat :=
  match r with
  | TR_cond1 r | TR_cond2 r | TR_while1 r => (route_size r).+1
  | TR_seqc r1 r2 => (route_size r1 + route_size r2).+1
  | _ => 1%N
  end.

Lemma route_size_ind (P : route -> Prop) :
  (forall n, (forall r, (route_size r < n)%N -> P r) ->
    forall r, route_size r = n -> P r) -> forall r, P r.
Proof.
move=>IH r.
have [n Pn]: exists n, route_size r = n by exists (route_size r).
by elim/ltn_ind: n r Pn=>n Pn; apply/IH=>r Pr; apply/(Pn _ Pr).
Qed.

Definition cast_value (t u : sort) (E : t = u) (v : value t) : value u :=
  let: erefl in _ = u := E return value u in v.

Fixpoint eval_route (r : route) (c : command)
    (i : store * 'End(Hq)) : option (store * 'End(Hq)) :=
  match r, c with
  | TR_skip, Skip => Some i
  | TR_assign, Assign t x e => Some ((i.1.[x <- eval e i.1])%M, i.2)
  | TR_random t v, Random u x p =>
      match asboolP (t = u) with
      | ReflectT E => Some ((i.1.[x <- cast_value E v])%M,
          probability_mass p i.1 (cast_value E v) *: i.2)
      | _ => None
      end
  | TR_measure t v, Measure u _ x q M =>
      match asboolP (t = QType u) with
      | ReflectT E => Some ((i.1.[x <- cast_value E v])%M,
          measurement_branches q M i.1 (cast_value E v) i.2)
      | _ => None
      end
  | TR_initial, Initialize u q phi =>
      Some (i.1, liftfso (initialso (tv2v q (esem phi i.1))) i.2)
  | TR_unitary, Unitary u q U =>
      Some (i.1, liftfso (formso (tf2f q q (esem U i.1))) i.2)
  | TR_cond1 r, Conditional b c1 c0 =>
      if eval b i.1 then eval_route r c1 i else None
  | TR_cond2 r, Conditional b c1 c0 =>
      if ~~ eval b i.1 then eval_route r c0 i else None
  | TR_while0, While b c => if ~~ eval b i.1 then Some i else None
  | TR_while1 r, While b c =>
      if eval b i.1 then eval_route r (Sequence c (While b c)) i else None
  | TR_seqc r1 r2, Sequence c1 c2 =>
      match eval_route r1 c1 i with
      | Some m => eval_route r2 c2 m
      | None => None
      end
  | _, _ => None
  end.

Lemma terminates_sequence c1 c2 s r m q s' r' :
  terminates c1 s r m q -> terminates c2 m q s' r' ->
  terminates (Sequence c1 c2) s r s' r'.
Proof.
move=>d1; elim: d1=>[c s0 r0 s1 r1 st | c c' s0 r0 s1 r1 s2 r2 st tail IH] d2.
- exact: (@TerminatesMore (Sequence c c2) c2 s0 r0 s1 r1 s' r'
    (@StepSequenceDone c c2 s0 r0 s1 r1 st) d2).
- exact: (@TerminatesMore (Sequence c c2) (Sequence c' c2) s0 r0 s1 r1 s' r'
    (@StepSequenceMore c c2 c' s0 r0 s1 r1 st) (IH d2)).
Qed.

Lemma eval_route_sound rt c s r s' r' :
  eval_route rt c (s,r) = Some (s',r') -> terminates c s r s' r'.
Proof.
elim: rt c s r s' r'=>[| |t v|rt IH|rt IH| |rt IH|r1 IH1 r2 IH2| | |t v]
  c s r s' r'.
- case: c=>//= [= <- <-]; apply: TerminatesDone; exact: StepSkip.
- case: c=>//= t x e; move=>[= <- <-]; apply: TerminatesDone; exact: StepAssign.
- case: c=>//= u x p; case: asboolP=>//= E; move=>[= <- <-].
  apply: TerminatesDone; exact: StepRandom.
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@TerminatesMore (Conditional b c1 c0) c1 s r s r s' r'
    (@StepIfTrue b c1 c0 s r Eb) (IH c1 s r s' r' H)).
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@TerminatesMore (Conditional b c1 c0) c0 s r s r s' r'
    (@StepIfFalse b c1 c0 s r Eb) (IH c0 s r s' r' H)).
- case: c=>//= b c0; case Eb: (eval b s)=>//=; move=>[= <- <-].
  exact: (@TerminatesDone _ _ _ _ _ (@StepWhileFalse b c0 s r Eb)).
- case: c=>//= b c0; case Eb: (eval b s)=>//= H.
  exact: (@TerminatesMore (While b c0) (Sequence c0 (While b c0)) s r s r s' r'
    (@StepWhileTrue b c0 s r Eb) (IH _ s r s' r' H)).
- case: c=>//= c1 c2; case E: (eval_route r1 c1 (s,r))=>[[m q]|] //= H.
  exact: (@terminates_sequence c1 c2 s r m q s' r' (IH1 _ _ _ _ _ E) (IH2 _ _ _ _ _ H)).
- case: c=>//= u q phi; move=>[= <- <-]; apply: TerminatesDone; exact: StepInitialize.
- case: c=>//= u q U; move=>[= <- <-]; apply: TerminatesDone; exact: StepUnitary.
- case: c=>//= u z x q M; case: asboolP=>//= E; move=>[= <- <-].
  apply: TerminatesDone; exact: StepMeasure.
Qed.

Lemma step_route_complete c s r c' s' r' (d : step c s r c' s' r') :
  forall rt o,
    (match c' with None => Some (s',r') | Some k => eval_route rt k (s',r') end) = Some o ->
    exists rr, eval_route rr c (s,r) = Some o.
Proof.
induction d; move=>rt o H.
- exists TR_skip; exact H.
- exists TR_assign; exact H.
- exists (TR_random i); rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- exists (TR_measure i); rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- exists TR_initial; exact H.
- exists TR_unitary; exact H.
- have [r1 Hr1] := IHd TR_skip (s',r') erefl.
  by exists (TR_seqc r1 rt); rewrite /= Hr1.
- case: rt H=>//= r1 r2.
  case E: (eval_route r1 c1' (s',r'))=>[[m q]|] //= H.
  have [r0 Hr0] := IHd r1 (m,q) E.
  by exists (TR_seqc r0 r2); rewrite /= Hr0.
- by exists (TR_cond1 rt); rewrite /= e.
- by exists (TR_cond2 rt); rewrite /= e.
- by exists (TR_while1 rt); rewrite /= e.
- exists TR_while0; by rewrite /= e.
Qed.

Lemma terminating_route c s r s' r' :
  terminates c s r s' r' -> exists rt, eval_route rt c (s,r) = Some (s',r').
Proof.
elim=>[c0 s0 r0 s1 r1 st | c0 c1 s0 r0 s1 r1 s2 r2 st tail [rt Hrt]].
- exact: step_route_complete st TR_skip (s1,r1) erefl.
- exact: step_route_complete st rt (s2,r2) Hrt.
Qed.

Definition opfun (c : command) (s : store) (rho : 'End(Hq)) (r : route)
    : {summable store -> 'End(Hq)} :=
  match eval_route r c (s,rho) with
  | Some o => sunit_def o.1 o.2
  | None => 0
  end.

Definition opsum (c : command) (s : store) (rho : 'End(Hq))
    : {summable store -> 'End(Hq)} := sum (opfun c s rho).

Definition operational_sum := opsum.

Lemma eval_route_ge0 (r : route) (c : command) (mi : store) (qi : 'End(Hq)) :
  0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route r c (mi,qi)).
Proof.
move=>Pq; case E: (eval_route r c (mi,qi))=>[[m q]|].
- change (0%:VF ⊑ q).
  exact (@terminates_positive c mi qi m q (@eval_route_sound r c mi qi m q E) Pq).
- exact Pq.
Qed.


Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Ltac exactltac := try (intros; match goal with
  | [ H : is_true ((0 : 'End(Hq)) ⊑ ?x) |- is_true ((0 : 'End(Hq)) ⊑ ?x) ] => exact H end).

Local Definition opfun_summable (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  0%:VF ⊑ qi -> (forall S, psum \`|opfun c mi qi| S <= `|qi|).
Local Definition opsum_norm_ub (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  0%:VF ⊑ qi -> `|opsum c mi qi| <= `|qi|.
Local Definition op_sem_eq (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  forall mo, 0%:VF ⊑ qi -> opsum c mi qi mo = denote c mi mo qi.
Local Definition ind_hyp (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  opfun_summable c mi qi /\ op_sem_eq c mi qi.

Lemma opfun_summable_norm_ub (c : command) (mi : cmem) (qi : 'End(Hq)) :
  opfun_summable c mi qi -> opsum_norm_ub c mi qi.
Proof.
move=>P1 Pq; rewrite /opsum.
have Ps: summable (opfun c mi qi). exists `|qi|. near=>S. by apply: P1.
rewrite (summablefE Ps). apply/(le_trans (summable_sum_ler_norm _)).
apply: etlim_le. apply: summable_norm_is_cvg. by apply: P1.
Unshelve. end_near.
Qed.

Lemma psum_lerG (I : choiceType) (T : numDomainType) (x : I -> T) (A B : {fset I}) :
  (forall i, i \in (B `\` A)%fset -> 0 <= x i) -> 
  (forall i, i \in (A `\` B)%fset -> x i <= 0) ->
    psum x A <= psum x B.
Proof.
move=>H1 H2.
rewrite -[A](fsetID B) -{3}[B](fsetID A) !psumU ?fdisjointID// fsetIC lerD2l.
apply/(le_trans (y := 0)); first rewrite -oppr_ge0 -psumN.
all: apply/sumr_ge0=>[[i/=+ _]].
by move=>/H2; rewrite fctE oppr_ge0. by move=>/H1.
Qed.

Lemma equal_OS_DS_skip (mi : cmem) (qi : 'End(Hq)) :
  ind_hyp Skip mi qi.
Proof.
split=>[Pq S|mo].
  apply/(le_trans (y := psum \`| opfun Skip mi qi | [fset TR_skip]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  by rewrite psum1/opfun/= sunit_normE.
rewrite /opsum (fin_supp_sum (S := [fset TR_skip])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite soE.
Qed. 

Lemma equal_OS_DS_assign (t : sort) (x : variable t) 
  (e : expression (value t)) (mi : cmem) (qi : 'End(Hq)) :
  ind_hyp (Assign x e) mi qi.
Proof.
split=>[Pq S|mo].
  apply/(le_trans (y := psum \`| opfun (Assign x e) mi qi | [fset TR_assign]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  by rewrite psum1/opfun/= sunit_normE.
rewrite /opsum (fin_supp_sum (S := [fset TR_assign])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite soE.
Qed.

Import Summable_Reindex.

Lemma equal_OS_DS_seqc (c1 c2: command) :
  (forall mi qi, ind_hyp c1 mi qi) ->
  (forall mi qi, ind_hyp c2 mi qi) ->
  forall mi qi, ind_hyp (Sequence c1 c2) mi qi.
move=>IH1 IH2.
pose h := (fun r => TR_seqc r.1 r.2).
pose h' := (fun r => match r with | TR_seqc r1 r2 => Some (r1,r2) | _ => None end).
have hK : pcancel h h'. by case.
have h'K : ocancel h' h. by case.
have PE: forall mi qi, 0%:VF ⊑ qi -> forall S1 S2,
  psum (fun r1 => psum (fun r2 => `|opfun (Sequence c1 c2) mi qi (TR_seqc r1 r2)|) S2) S1 <= `|qi|.
  move=>/=mi qi Pq S1 S2. rewrite/opfun/=/psum.
  move: (IH1 mi qi)=>[]/(_ Pq S1)+ _; apply: le_trans.
  apply: ler_sum=>/= i _; rewrite /opfun.
  case E: (eval_route (fsval i) c1 (mi, qi))=>[[a b]|] /=.
  rewrite sunit_normE. move: (IH2 a b)=>[] P1 _. apply: P1.
  move: (eval_route_ge0 (fsval i) c1 mi Pq); rewrite E/=; exactltac.
  by rewrite big1 normr0.
move=>mi qi.
have Pf : Hf h' (opfun (Sequence c1 c2) mi qi) by case.
have Pfn : Hf h' \`| opfun (Sequence c1 c2) mi qi|.
  by case=>//=; rewrite /opfun/= ?normr0.
have Q1: opfun_summable (Sequence c1 c2) mi qi.
move=>Pq/= S; rewrite (psum_Sj hK h'K (TR_skip,TR_skip))//=.
set T := (Sj h' (TR_skip, TR_skip) S).
pose A := (fst @` T)%fset. pose B := (snd @` T)%fset.
apply/(le_trans (y := \sum_(i <- A)\sum_(j <- B) `|opfun (Sequence c1 c2) mi qi (h (i, j))|)).
rewrite pair_big_dep_cond/= big_seq_fsetE/=. apply: psum_ler=>//.
apply/fsubsetP=>[[/=a b PT]]/=; rewrite !inE/= !andbT /A/B; apply/andP; split;
by apply/imfsetP; exists (a,b).
rewrite big_seq_fsetE; under eq_bigr do rewrite big_seq_fsetE.
by apply: PE.

split=>//; rewrite/op_sem_eq.
pose hx := (fun r : route * route => 
  match eval_route r.1 c1 (mi, qi) with
  | Some t => match eval_route r.2 c2 t with
            | Some t => sunit_def t.1 t.2
            | None => 0
            end
  | None => 0 end : {summable _ -> _}).
have Ph: (opfun (Sequence c1 c2) mi qi \o h)%FUN = hx.
  by apply/funext=>[[r1 r2]]/=; rewrite/opfun/hx/=; case: (eval_route r1 c1 (mi, qi)).
move=>mo Pq.
have Pss: summable (opfun (Sequence c1 c2) mi qi).
exists `|qi|. near=>J. by apply: Q1.
rewrite/opsum (@sum_reindex _ _ _ _ _ h h').
  1,2,3: by case.
  by apply/(reindex_summableP_simple (h' := h') _ _ (TR_skip,TR_skip)).
rewrite Ph.
have ->: sum hx = sum (fun r1 => sum (fun r2 => hx (r1,r2))).
  apply: pseries2_exchange_lim_pair.
  exists `|qi|=>/= Si Sj.
  apply/(le_trans _ (PE mi _ Pq Si Sj))/ler_sum=>i _; apply: ler_sum=>j _.
  by rewrite/hx/opfun/=; case: (eval_route (fsval i) c1 (mi, qi)).
rewrite sum_summableE.
  apply: norm_bounded_cvg. exists `|qi|. near=>J.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  rewrite/hx/opfun/=/normf/=.
  case E: (eval_route (val i) c1 (mi, qi))=>[[a1 a2]|] /=;
    last by rewrite summable_sum_cst0.
  rewrite -/(opfun c2 a1 a2) sunit_normE.
  apply: (opfun_summable_norm_ub (proj1 (IH2 a1 a2))).
  move: (eval_route_ge0 (fsval i) c1 mi Pq); rewrite E/=; exactltac.
rewrite/hx/= (eq_sum (g := (fun i => match eval_route i c1 (mi, qi) with
| Some t => denote c2 t.1 mo t.2 | None => 0 end))).
  move=>r1; case E: (eval_route r1 c1 (mi, qi))=>[[a1 a2]|] /=.
  apply: (proj2 (IH2 _ _)).
  move: (eval_route_ge0 r1 c1 mi Pq); rewrite E/=; exactltac.
  by rewrite summable_sum_cst0 summableE.
rewrite/slet_def sum_summable_soE.
  apply: norm_bounded_cvg. 
  move: (slet_norm_uboundW (denote c1) (denote c2) mi)=>[M0/(_ [fset mo]%fset) PM].
  exists M0; near=>J; by move: (PM J); rewrite psum1.
under [in RHS]eq_sum do rewrite soE -(proj2 (IH1 mi qi) _ Pq).
rewrite [RHS](eq_sum (g := fun m => sum ((fun m r => 
  match eval_route r c1 (mi, qi) with
  | Some t => if t.1 == m then denote c2 m mo t.2 else 0
  | None => 0 end) m))).
move=>m. rewrite sum_summableE.
  apply: norm_bounded_cvg; exists `|qi|; near=>J; apply: (proj1 (IH1 mi qi) Pq).
rewrite cvg_linear_sum.
  apply: norm_bounded_cvg; exists `|qi|; near=>J.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  by move: (psum_norm_ler_norm (opfun c1 mi qi (val i)) [fset m]%fset); rewrite psum1.
f_equal. apply/funext=>r; rewrite/=.
rewrite /opfun /=.
case E: (eval_route r c1 (mi, qi))=>[p|] /=;
  last by rewrite ?summableE linear0.
by rewrite/=/sunit_def eq_sym; case: eqP=>//; rewrite linear0.
rewrite pseries2_exchange_lim.
  exists `|qi|=>Mm J; rewrite/psum exchange_big/=.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  rewrite/opfun/=.
  case Er: (eval_route (val i) c1 (mi, qi))=>[p|] /=;
    last by rewrite !normr0 big1.
  rewrite sunit_normE; case E: (p.1 \in Mm).
  rewrite (bigD1 [` E])//= eqxx big1=>[j|].
  by rewrite -(inj_eq (val_inj))/= eq_sym=>/negPf ->; rewrite normr0.
  move: (eval_route_ge0 (val i) c1 mi Pq); rewrite Er/==>Pp.
  by rewrite addr0 !psd_trfnorm ?qo_trlfE ?cp_psdP ?psdlfE ?Pp.
  rewrite big1// =>[[j/= Pj _]]; case: eqP=>[Pe|]; last by rewrite normr0.
  by rewrite -Pe in Pj; rewrite Pj in E.
f_equal. apply/funext=>r.
case: (eval_route r c1 (mi, qi))=>[[a1 a2]|]; last by rewrite summable_sum_cst0.
rewrite/= (fin_supp_sum (S := [fset a1]%fset)) ?psum1 ?eqxx// =>i;
by rewrite inE eq_sym=>/negPf->.
Unshelve. all: end_near.
Qed.

Lemma equal_OS_DS_abort (mi : cmem) (qi : 'End(Hq)) : ind_hyp Abort mi qi.
Proof.
split=>??; first by rewrite/psum big1// =>i _; rewrite/opfun/=; case: (fsval i); rewrite/= normr0.
by rewrite/= abort_semE soE /opsum (fin_supp_sum (S := fset0)) ?psum0//=; case.
Qed.

Lemma equal_OS_DS_if e c1 c2 :
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c1 mi qi) ->
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c2 mi qi) ->
  forall (mi : cmem) (qi : 'End(Hq)), ind_hyp (Conditional e c1 c2)%V mi qi.
Proof.
move=>IHc1 IHc2 mi qi.
case E: (eval e mi); rewrite/opsum.
  pose h := (fun r => TR_cond1 r).
  pose h' := (fun r => match r with | TR_cond1 r => Some r | _ => None end).
  pose hx := opfun c1 mi qi.
  split=>[Pq S|mo Pq].
    rewrite (@psum_Sj _ _ h h' _ _ (TR_skip))/opfun//=. by case.
    by case=>// r/=; rewrite ?E/= normr0.
    by rewrite E; apply: (proj1 (IHc1 mi qi) Pq).
  have shx : summable hx by exists `|qi|; near=>J; apply: (proj1 (IHc1 mi qi) Pq).
  have Ph : ((fun r : route => match eval_route r (Conditional e c1 c2)%V (mi, qi) with
                                    | Some t => sunit_def t.1 t.2 : {summable _ -> _}
                                    | None => 0
                                    end) \o h)%FUN = hx.
    by apply/funext=>r/=; rewrite E.
  rewrite/opsum (@sum_reindex _ _ _ _ _ h h')=>[//||||]; first by case.
  by case=>// r/=; rewrite/opfun/= E/=.
  by rewrite Ph.
  by rewrite Ph/hx/= -/(eval e mi) E; apply (proj2 (IHc1 mi qi) mo Pq).
pose h := (fun r => TR_cond2 r).
pose h' := (fun r => match r with | TR_cond2 r => Some r | _ => None end).
pose hx := opfun c2 mi qi.
split=>[Pq S|mo Pq].
  rewrite (@psum_Sj _ _ h h' _ _ (TR_skip))/opfun//=. by case.
  by case=>// r/=; rewrite ?E/= normr0.
  by rewrite E; apply: (proj1 (IHc2 mi qi) Pq).
have shx : summable hx by exists `|qi|; near=>J; apply: (proj1 (IHc2 mi qi) Pq).
have Ph : ((fun r : route => match eval_route r (Conditional e c1 c2)%V (mi, qi) with
                                    | Some t => sunit_def t.1 t.2 : {summable _ -> _}
                                    | None => 0
                                    end) \o h)%FUN = hx.
  by apply/funext=>r/=; rewrite E.
rewrite/opsum (@sum_reindex _ _ _ _ _ h h')=>[//||||]; first by case.
by case=>// r/=; rewrite/opfun/= E/=.
by rewrite Ph.
by rewrite Ph/hx/= -/(eval e mi) E; apply (proj2 (IHc2 mi qi) mo Pq).
Unshelve. all: end_near.
Qed.

Fixpoint route_W_size r :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => (route_W_size r2).+1
  | _ => 0%N
  end.

Fixpoint route_WC_size r :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => (route_WC_size r2).+1
  | TR_cond1 (TR_seqc r1 r2) => (route_WC_size r2).+1
  | _ => 0%N
  end.

Lemma route_WC_size_ind (P : route -> Prop) :
  (forall n, (forall r, (route_WC_size r < n)%N -> P r) -> 
    forall r, route_WC_size r = n -> P r) -> forall r, P r.
Proof.
move=>IH r.
have [n Pn]: exists n, route_WC_size r = n 
  by exists (route_WC_size r).
by elim/ltn_ind: n r Pn=>n Pn; apply/IH=>r Pr; apply/(Pn _ Pr).
Qed.

Fixpoint route_W2C r : route :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => TR_cond1 (TR_seqc r1 (route_W2C r2))
  | TR_while0 => TR_cond2 TR_skip
  | TR_cond1 (TR_seqc r1 r2) => TR_while1 (TR_seqc r1 (route_W2C r2))
  | TR_cond2 TR_skip => TR_while0
  | _ => r
  end.

Lemma route_W2CK : cancel route_W2C route_W2C.
Proof.
elim/route_WC_size_ind=>n IH.
by case=>//; case=>//= r1 r2 P; do ! f_equal; apply: IH; rewrite -P.
Qed.

Fixpoint while_syn_iter e c n :=
  match n with
  | 0%N => Abort
  | S n => Conditional e (Sequence c (while_syn_iter e c n)) Skip
  end.

Lemma eval_route_WE e c r n :
  (route_W_size r < n)%N -> forall mi qi, 
    eval_route r (While e c) (mi,qi) = eval_route (route_W2C r) (while_syn_iter e c n) (mi,qi).
Proof.
elim: n r=>//= n IH.
case=>//=; case=>//=; intros; case: (eval e mi)=>//.
by case: (eval_route r1 c (mi, qi))=>//[[a1 a2]]; apply/IH/H.
Qed.

Lemma eval_route_WEN e c r n :
  (route_W_size r >= n)%N -> forall mi qi, 
    eval_route (route_W2C r) (while_syn_iter e c n) (mi,qi) = None.
Proof.
elim: n r=>//=[r _ mi qi|n IH r Pr mi qi].
case: (route_W2C r)=>//.
case: r Pr=>//=; case=>//= r1 r2; rewrite ltnS=>Pn.
case: (eval e mi)=>//; case: (eval_route r1 c (mi, qi))=>//[[a1 a2]].
by rewrite IH.
Qed.

Lemma equal_OS_DS_while_syn_iter e c:
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall n mi qi, ind_hyp (while_syn_iter e c n) mi qi.
Proof.
move=>Hc; elim=>/=.
apply: equal_OS_DS_abort.
move=>n IH; apply: equal_OS_DS_if.
by apply: equal_OS_DS_seqc.
apply: equal_OS_DS_skip.
Qed.

Lemma equal_OS_DS_while_sem_iter e c:
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall n mi qi mo, 0%:VF ⊑ qi ->
  opsum (while_syn_iter e c n) mi qi mo = 
  while_sem_iter (translate_expr e) (denote c) n mi mo qi.
Proof.
move=>Hc n mi qi mo Pq.
rewrite (proj2 (equal_OS_DS_while_syn_iter e Hc n mi qi) mo Pq).
do ! f_equal; by elim: n=>//= n->.
Qed.

Lemma equal_OS_DS_while e c :
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall (mi : cmem) (qi : 'End(Hq)), ind_hyp (While e c) mi qi.
Proof.
move=>IH.
have P0: forall mi qi,  opfun_summable (While e c) mi qi.
  move=>mi qi Pq S; rewrite/opfun.
  pose n := (\max_(i <- (route_W_size @` S)%fset) i).+1.
  apply/(le_trans _ (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq (route_W2C @` S)%fset)).
  rewrite [X in _ <= X]psum_seq_fsetE big_imfset=>[?? _ _|]; first by apply/(can_inj route_W2CK).
  rewrite-psum_seq_fsetE; apply/ler_sum=>i _.
  suff >/(eval_route_WE e c)/(_ mi qi)->: (route_W_size (val i) < n)%N by [].
  have Phi: route_W_size (val i) \in (route_W_size  @` S)%fset.
  by apply/imfsetP; exists (val i)=>//; case: i.
  by rewrite/n ltnS big_seq_fsetE/= (bigmax_sup [`Phi]%fset)//.
move=>mi qi; split=>// mo Pq.
rewrite /opsum sum_summableE.
  by apply/norm_bounded_cvg; exists `|qi|; near=>J; apply: P0.
rewrite -(summable_sigma_nat_lim route_W_size).
  exists `|qi|. near=>J. apply: (le_trans _ (P0 mi qi Pq J)).
  apply/ler_sum=>i _; 
  by move: (psum_norm_ler_norm (opfun (While e c) mi qi (val i)) [fset mo]%fset); rewrite psum1.
rewrite -while_sem_limEEE -/denote.
apply: eq_lim=>n.
rewrite -equal_OS_DS_while_sem_iter//.
rewrite/opsum sum_summableE.
  apply/norm_bounded_cvg; exists `|qi|; near=>J.
  apply: (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq J).
pose h := (fun i => route_W2C (val i)) 
  : {i : route | (route_W_size i < n)%N} -> route.
pose h' := (fun i => match asboolP (route_W_size (route_W2C i) < n)%N with
  | ReflectT Q => Some (exist (fun j => (route_W_size j < n)%N) _ Q)
  | ReflectF _ => None end).
rewrite -(@sum_reindexV _ _ _ _ _ h h')=>[[i/=Pi]|i|/=i||].
- by rewrite/h/h'/= route_W2CK; case: asboolP=>// p; rewrite (eq_irrelevance Pi p).
- by rewrite/h/h'/=; case: asboolP=>//= p; rewrite route_W2CK.
- rewrite/h'; case: asboolP=>//=/negP+ _; rewrite -leqNgt/opfun;
  by move=>/(eval_route_WEN e c)/(_ mi qi); rewrite route_W2CK=>->; rewrite summableE.
- exists `|qi|; near=>J.
  apply/(le_trans _ (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq J)).
  apply/ler_sum=>i _. 
  by move: (psum_norm_ler_norm (opfun (while_syn_iter e c n) mi qi (val i)) [fset mo]%fset); rewrite psum1.
- apply: eq_sum=>[[i Pi]].
- by rewrite/opfun (eval_route_WE _ _ Pi)/=/h/=.
Unshelve. all: end_near.
Qed.


(* A generic atomic command, encoded by outcome-labelled routes.  These
   hypotheses are the primitive's defining equations, discharged below for
   each language constructor; no correctness judgment is postulated. *)
Lemma atomic_route_adequacy (I : choiceType) (i0 : I)
    (f : {vdistr I -> 'SO(Hq)}) (h : I -> store)
    (enc : I -> route) (dec : route -> option I) c mi :
  pcancel enc dec -> ocancel dec enc ->
  (forall qi r, eval_route r c (mi,qi) =
    omap (fun i => (h i, f i qi)) (dec r)) ->
  denote c mi = sdlet_vdistr h f -> forall qi, ind_hyp c mi qi.
Proof.
move=>encK decK Eeval Esem qi; split=>[Pq S|mo Pq].
  rewrite (psum_Sj encK decK i0).
    by move=>r Hr; rewrite /opfun Eeval Hr /= normr0.
  rewrite /psum.
  under eq_bigr do rewrite /opfun Eeval encK /= sunit_normE.
  exact: (CQInstrument.instrument_psum_bound f Pq).
have Eout : (opfun c mi qi \o enc)%FUN =
    (CQInstrument.instrument_outputs f h Pq : I -> {summable store -> 'End(Hq)}).
  by apply/funext=>i; rewrite /comp /opfun Eeval encK.
rewrite /opsum (sum_reindex encK decK).
  by move=>r Hr; rewrite /opfun Eeval Hr.
  by rewrite Eout; apply: summablefP.
by rewrite Eout CQInstrument.instrument_sumE -Esem.
Qed.

Definition decode_random (t : sort) (r : route) : option (value t) :=
  match r with
  | TR_random u v => match asboolP (u = t) with
      | ReflectT E => Some (cast_value E v) | _ => None end
  | _ => None
  end.

Definition decode_measure (t : sort) (r : route) : option (value t) :=
  match r with
  | TR_measure u v => match asboolP (u = t) with
      | ReflectT E => Some (cast_value E v) | _ => None end
  | _ => None
  end.

Lemma random_encodeK t : pcancel (@TR_random t) (decode_random t).
Proof. move=>v; rewrite /decode_random; case: asboolP=>[E|//]; by rewrite (eq_irrelevance E erefl). Qed.
Lemma random_decodeK t : ocancel (decode_random t) (@TR_random t).
Proof. case=>// u v; rewrite /decode_random; case: asboolP=>//= E; by case: t / E. Qed.
Lemma measure_encodeK t : pcancel (@TR_measure t) (decode_measure t).
Proof. move=>v; rewrite /decode_measure; case: asboolP=>[E|//]; by rewrite (eq_irrelevance E erefl). Qed.
Lemma measure_decodeK t : ocancel (decode_measure t) (@TR_measure t).
Proof. case=>// u v; rewrite /decode_measure; case: asboolP=>//= E; by case: t / E. Qed.

Lemma equal_OS_DS_random t (x : variable t) p mi qi :
  ind_hyp (Random x p) mi qi.
Proof.
refine (@atomic_route_adequacy (value t) (witness (value t))
  (sdistr Hq (probability_mass p mi)) (fun i => (mi.[x <- i])%M)
  (@TR_random t) (decode_random t) (Random x p) mi
  (@random_encodeK t) (@random_decodeK t) _ _ qi).
- move=>rho; case=>//= u v; rewrite /decode_random; case: asboolP=>//= E.
  by rewrite /sdistr_def !soE.
- by [].
Qed.

Lemma equal_OS_DS_measure (t u : qType) (x : variable (QType t))
    (q : wf_qreg u) M mi qi :
  ind_hyp (@Measure t u x q M) mi qi.
Proof.
refine (@atomic_route_adequacy (value (QType t)) (witness (value (QType t)))
  (measurement_branches q M mi) (fun i => (mi.[x <- i])%M)
  (@TR_measure (QType t)) (decode_measure (QType t)) (Measure x q M) mi
  (@measure_encodeK (QType t)) (@measure_decodeK (QType t)) _ _ qi).
- by move=>rho; case=>//= z v; rewrite /decode_measure; case: asboolP.
- by [].
Qed.

Lemma equal_OS_DS_initial u (q : wf_qreg u) phi mi qi :
  ind_hyp (Initialize q phi) mi qi.
Proof.
split=>[Pq S|mo _].
  apply/(le_trans (y := psum \`| opfun (Initialize q phi) mi qi | [fset TR_initial]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  have Pqi : qi \is psdlf by rewrite psdlfE.
  have Po : (liftfso (initialso (tv2v q (esem phi mi))) qi) \is psdlf.
    rewrite psdlfE; exact: (step_positive (@StepInitialize u q phi mi qi) Pq).
  rewrite psum1/opfun/= sunit_normE (psd_trfnorm Po) (psd_trfnorm Pqi).
  exact: (step_trace_le (@StepInitialize u q phi mi qi) Pq).
rewrite/= /opsum (fin_supp_sum (S := [fset TR_initial])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite// soE.
Qed.

Lemma equal_OS_DS_unitary u (q : wf_qreg u) U mi qi :
  ind_hyp (Unitary q U) mi qi.
Proof.
split=>[Pq S|mo _].
  apply/(le_trans (y := psum \`| opfun (Unitary q U) mi qi | [fset TR_unitary]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  have Pqi : qi \is psdlf by rewrite psdlfE.
  have Po : (liftfso (formso (tf2f q q (esem U mi))) qi) \is psdlf.
    rewrite psdlfE; exact: (step_positive (@StepUnitary u q U mi qi) Pq).
  rewrite psum1/opfun/= sunit_normE (psd_trfnorm Po) (psd_trfnorm Pqi).
  exact: (step_trace_le (@StepUnitary u q U mi qi) Pq).
rewrite/= /opsum (fin_supp_sum (S := [fset TR_unitary])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite// soE.
Qed.

Theorem equal_OS_DS c mi qi : ind_hyp c mi qi.
Proof.
elim: c mi qi=>[| |t x e|t x p|t u x q M|u q phi|u q U|
  c1 IH1 c2 IH2|b c1 IH1 c0 IH0|b c IH] mi qi.
- exact: equal_OS_DS_skip.
- exact: equal_OS_DS_abort.
- exact: equal_OS_DS_assign.
- exact: equal_OS_DS_random.
- exact: equal_OS_DS_measure.
- exact: equal_OS_DS_initial.
- exact: equal_OS_DS_unitary.
- exact (@equal_OS_DS_seqc c1 c2 IH1 IH2 mi qi).
- exact (@equal_OS_DS_if b c1 c0 IH1 IH0 mi qi).
- exact (@equal_OS_DS_while b c IH mi qi).
Qed.

Theorem operational_denotational c mi qi mo :
  0%:VF ⊑ qi -> opsum c mi qi mo = denote c mi mo qi.
Proof. exact: (proj2 (equal_OS_DS c mi qi)). Qed.

Theorem operational_summable c mi qi :
  0%:VF ⊑ qi -> summable (opfun c mi qi).
Proof.
move=>Pq; exists `|qi|; near=>J.
exact: (proj1 (equal_OS_DS c mi qi) Pq J).
Unshelve. end_near.
Qed.

End ClassicalOperational.
