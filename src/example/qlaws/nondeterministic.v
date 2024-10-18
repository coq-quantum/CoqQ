From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import -(notations)forms topology.
From mathcomp.analysis Require Import reals normedtype sequences.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import Relation_Definitions.
Require Import -(notations)Setoid.
(* topology and setoid has notation conflicts *)
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra mcaextra notation mxpred extnum ctopology summable.
Require Import hermitian quantum hspace hspace_extra inhabited prodvect tensor qreg qmem cpo qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.qlaws Require Import basic_def convex circuit.
Import Order.TTheory GRing.Theory Num.Theory Num.Def HermitianTopology.
Import DefaultQMem.Exports.

(****************************************************************************)
(*            Semantics and QLaws for Recursive Quantum Program             *)
(****************************************************************************)

Local Notation C := hermitian.C.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(****************************************************************************)
(*                convex set of operators and super operator                *)
(*           conv (A \o B) = conv (conv A \o conv B)                        *)
(*           conv (A :o B) = conv (conv A :o conv B)                        *)
(****************************************************************************)
Section SetCompso.
Variable (U : chsType).

Definition set_compso (A B : set 'SO(U)) :=
  [set a :o b | a in A & b in B].
Infix "`:o`" := set_compso (at level 50).

Lemma set_compso1l : left_id  [set \:1] set_compso.
Proof.
move=>A; rewrite /set_compso image2_set1; apply/seteqP; split=>i/=.
by move=>[x Px]; rewrite comp_so1l=><-.
by move=>Pi; exists i=>//; rewrite comp_so1l.
Qed.

Lemma set_compso1r : right_id  [set \:1] set_compso.
Proof.
move=>A; rewrite /set_compso image2_set1; apply/seteqP; split=>i/=.
by move=>[x Px]; rewrite comp_so1r=><-.
by move=>Pi; exists i=>//; rewrite comp_so1r.
Qed.

Lemma set_compsoA : associative set_compso.
Proof.
move=>A B C; apply/seteqP; split=>i.
  move=>[a Pa][?][b Pb][c Pc]<-<-.
  exists (a :o b); first by exists a=>//; exists b.
  by exists c=>//; rewrite comp_soA.
move=>[?][a Pa][b Pb]<-[c Pc]<-.
exists a=>//; exists (b :o c); first by exists b=>//; exists c.
by rewrite comp_soA.
Qed.

HB.instance Definition _ := Monoid.isLaw.Build (set 'SO(U)) [set \:1]
  set_compso set_compsoA set_compso1l set_compso1r.

Lemma set_compsoxl u A : [set u] `:o` A = [set u :o i | i in A].
Proof. by rewrite /set_compso image2_set1. Qed.

Lemma set_compsoxr u A : A `:o` [set u] = [set i :o u | i in A].
Proof. by rewrite /set_compso image2_set1. Qed.

Lemma set_compso_le A B C D : 
  A `<=` C -> B `<=` D -> A `:o` B `<=` C `:o` D.
Proof.
move=>P1 P2 ? [a Pa][b Pb]<-; exists a; first by apply P1.
by exists b=>//; apply P2.
Qed.
Lemma set_compso_lel A B C :
  B `<=` C -> A `:o` B `<=` A `:o` C.
Proof. by move=>P1; apply/set_compso_le. Qed.
Lemma set_compso_ler A B C :
  B `<=` C -> B `:o` A `<=` C `:o` A.
Proof. by move=>P1; apply/set_compso_le. Qed.

Lemma set_compso0l A : A !=set0 -> 0 `:o` A = 0.
Proof.
move=>[x Px]; apply/seteqP; split=>?; rewrite /GRing.zero/=.
by move=>[y]/=->[]??<-; rewrite comp_so0l.
by move=>->; exists 0=>//; exists x=>//; rewrite comp_so0l.
Qed.

Lemma set_compso0r A : A !=set0 -> A `:o` 0 = 0.
Proof.
move=>[x Px]; apply/seteqP; split=>?; rewrite /GRing.zero/=.
by move=>[??][?]/=-><-; rewrite comp_so0r.
by move=>->; exists x=>//; exists 0=>//; rewrite comp_so0r.
Qed.

Lemma set_compsoDl (A B C : set 'SO(U)) : 
  A `:o` (B + C) `<=` A `:o` B + (A `:o` C).
Proof.
move=>x[a Pa][?][/=b Pb][c Pc]<-<-.
exists (a :o b); first by exists a=>//; exists b.
exists (a :o c); first by exists a=>//; exists c.
by rewrite comp_soDr.
Qed.

Lemma set_compsoDr (A B C : set 'SO(U)) : 
  (A + B) `:o` C `<=` A `:o` C + (B `:o` C).
Proof.
move=>x[?][/=a Pa][b Pb]<-[c Pc]<-.
exists (a :o c); first by exists a=>//; exists c.
exists (b :o c); first by exists b=>//; exists c.
by rewrite comp_soDl.
Qed.

Lemma set_compsoxDl c (A B : set 'SO(U)) : 
  [set c] `:o` (A + B) = [set c] `:o` A + ([set c] `:o` B).
Proof.
rewrite !set_compsoxl; apply/seteqP; split=>?/=.
move=>[?][a Pa][b Pb]<-<-; exists (c :o a); first by exists a.
exists (c :o b); first by exists b. by rewrite comp_soDr.
move=>[?][a Pa]<-[?][b Pb]<-<-; exists (a + b).
by exists a=>//; exists b. by rewrite comp_soDr.
Qed.

Lemma set_compsoxDr c (A B : set 'SO(U)) : 
  (A + B) `:o` [set c] = A `:o` [set c] + (B `:o` [set c]).
Proof.
rewrite !set_compsoxr; apply/seteqP; split=>?/=.
move=>[?][a Pa][b Pb]<-<-; exists (a :o c); first by exists a.
exists (b :o c); first by exists b. by rewrite comp_soDl.
move=>[?][a Pa]<-[?][b Pb]<-<-; exists (a + b).
by exists a=>//; exists b. by rewrite comp_soDl.
Qed.

Lemma set_compsoZl a A B :
  a `*:` (A `:o` B) = (a `*:` A) `:o` B.
Proof.
apply/seteqP; split=>/=?.
move=>[/=?][x Px][y Py]<-<-; exists (a *: x); first by exists x.
by exists y=>//; rewrite comp_soZl.
move=>[?][/=x Px]<-[y Py]<-; exists (x :o y); last by rewrite comp_soZl.
by exists x=>//; exists y.
Qed.

Lemma set_compsoZr a A B :
  a `*:` (A `:o` B) = A `:o` (a `*:` B).
Proof.
apply/seteqP; split=>/=?.
move=>[/=?][x Px][y Py]<-<-; exists x=>//.
exists (a *: y); by [exists y | rewrite comp_soZr].
move=>[x Px][?][/= y Py]<-<-.
exists (x :o y); last by rewrite comp_soZr.
by exists x=>//; exists y.
Qed.

Lemma conv_compso A B :
  conv ((conv A) `:o` (conv B)) = conv (A `:o` B).
Proof.
apply/seteqP; split.
  rewrite -[conv (A `:o` B)]conv_idem; apply/conv_le_hom.
  move=>x [xa [Fa][ca][fa][Pa1][Pa2][Pa3]Pa4] [xb [Fb][cb][fb][Pb1][Pb2][Pb3]Pb4] <-.
  exists (Fa * Fb)%type.
  exists (fun i=>ca i.1 * cb i.2).
  exists (fun i=>fa i.1 :o fb i.2).
  do ! split.
  - move=>[i1 i2]/=; rewrite mulr_ge0 ?mulr_ile1//; 
    by move: (Pa1 i1) (Pb1 i2)=>/andP[]++/andP[].
  - by rewrite pair_bigV/= -Pa2; apply eq_bigr=>i _; rewrite -mulr_sumr Pb2 mulr1.
  - move=>[i1 i2]; rewrite inE/=;
    exists (fa i1); first by move: (Pa3 i1); rewrite inE.
    by exists (fb i2)=>//; move: (Pb3 i2); rewrite inE.
  - under eq_bigr do rewrite -scalerA -comp_soZr -comp_soZl.
    rewrite Pa4 Pb4 pair_bigV/= linear_suml; apply eq_bigr=>i _.
    by rewrite/= linear_sumr.
by apply/conv_le_hom/set_compso_le; apply/conv_le.
Qed.
End SetCompso.

End ConvexAlgebra.
End Convex.

Infix "`*:`" := set_scale (at level 40) : lfun_scope.
Infix "`\o`" := set_comp (at level 50) : lfun_scope.
Infix "`:o`" := set_compso (at level 50) : lfun_scope.

(*****************************************************************************)
(*                     nondeterministic without recursive                    *)
(*****************************************************************************)

Inductive cmd_  : Type :=
    | skip_ 
    | abort_
    | init_      T of qreg T & 'NS('Ht T)
    | circuit_   of ucmd_
    | seqc_      of cmd_ & cmd_
    | cond_      T (f: finType) (x : qreg T) of 'QM(f;'Ht T) & (f -> cmd_)
    | while_     T (x : qreg T) of 'QM(bool;'Ht T) & cmd_
    | nchoice_   of cmd_ & cmd_
    | pchoice_   of {p : C | 0 <= p <= 1} & cmd_ & cmd_.

Fixpoint no_nchoice_ (c : cmd_) : bool :=
  match c with
  | skip_ => true
  | abort_ => true 
  | init_  _ _ _ => true 
  | circuit_ _ => true 
  | seqc_ c1 c2 | pchoice_ _ c1 c2 => (no_nchoice_ c1) && (no_nchoice_ c2)
  | cond_  _ _ _ _ c => [forall i, (no_nchoice_ (c i))]
  | while_ _ _ _ c => no_nchoice_ c
  | nchoice_ _ _ => false
  end.

HB.lock
Definition cond2_ T (x : qreg T) (M : 'QM(bool; 'Ht T)) (c0 c1 : cmd_) :=
  cond_ x M (fun b => if b then c1 else c0).

Notation "'skip'" := skip_ (in custom cmd at level 0).
Notation "'abort'" := abort_ (in custom cmd at level 0).
Notation " c1 ';;' c2 " := (seqc_ c1 c2) (in custom cmd at level 30, c2 at next level, 
  left associativity, format "'[v' c1  ;;  '/' c2 ']'").
Notation " c1 '⊔' c2 " := (nchoice_ c1 c2) (in custom cmd at level 10, c2 at next level, 
  left associativity, format "'[v' c1  ⊔  '/'   c2  ']'").
Notation " c1 '⊔_(' p ) c2 " := (pchoice_ p c1 c2) (in custom cmd at level 10, c2 at next level, 
  left associativity, format "c1  '⊔_(' p )  c2").
Notation "[ 'cir' c ]" := (circuit_ c) (in custom cmd at level 20,
  format "[ 'cir'  c  ]").
Notation "[ x ] ':=' v" := (init_ x v)
  (in custom cmd at level 20, x custom reg, v constr,
  format "[ x ]  ':='  v").
Notation "'If' M [ x ] '=' i 'then' F 'fI'" := (cond_ x M (fun i => F))
  (in custom cmd at level 20, x custom reg, M constr, i name, F constr,
  format "'[v' 'If'  M [ x ]  '='  i  'then'  '/' '['     F ']' '/' 'fI' ']'").
Notation "'While' M [ x ] '=' '1' 'do' c 'od'" := (while_ x M c)
  (in custom cmd at level 20, x custom reg, M constr,
  format "'[v' 'While'  M [ x ]  '='  '1'  'do'  '/' '['     c ']' '/'  'od' ']'").
Notation " c0 '◁' M [ x ] '▷' c1 " := (cond2_ x M c0 c1)
  (in custom cmd at level 20, x custom reg, M constr,
  format "c0  '◁'  M [ x ]  '▷'  c1").
Notation " c0 '◁' [ x ] '▷' c1 " := (cond2_ x bvmeas_reverse_coercion1 c0 c1)
  (in custom cmd at level 20, x custom reg, only printing,
  format "c0  '◁'  [ x ]  '▷'  c1").
Notation " c0 '◁' [ x ] '▷' c1 " := (cond2_ x bvmeas_reverse_coercion c0 c1)
  (in custom cmd at level 20, x custom reg,
  format "c0  '◁'  [ x ]  '▷'  c1").
Notation "M [ x ] '▷' c " := (cond2_ x M skip_ c)
  (in custom cmd at level 20, x custom reg,
  format "M [ x ]  '▷'  c").
Notation "[ x ] '▷' c" := (cond2_ x bvmeas_reverse_coercion1 skip_ c)
  (in custom cmd at level 20, x custom reg, only printing,
  format "[ x ]  '▷'  c").
Notation "[ x ] '▷' c" := (cond2_ x bvmeas_reverse_coercion skip_ c)
  (in custom cmd at level 20, x custom reg,
  format "[ x ]  '▷'  c").
Notation "M [ x ] '*' c " := (while_ x M c)
  (in custom cmd at level 20, x custom reg,
  format "M [ x ]  '*'  c").
Notation "[ x ] '*' c " := (while_ x bvmeas_reverse_coercion1 c)
  (in custom cmd at level 20, x custom reg, only printing,
  format "[ x ]  '*'  c").
Notation "[ x ] '*' c " := (while_ x bvmeas_reverse_coercion c)
  (in custom cmd at level 20, x custom reg,
  format "[ x ]  '*'  c").
Notation "''[' M [ x ] ]" := (cond2_ x M skip_ skip_)
  (in custom cmd at level 20, x custom reg, M constr,
  format "''['  M [ x ]  ]").
Notation "''(' M [ x ] ]" := (cond2_ x M abort_ skip_)
  (in custom cmd at level 20, x custom reg, M constr,
  format "''('  M [ x ]  ]").
Notation "''[' M [ x ] )" := (cond2_ x M skip_ abort_)
  (in custom cmd at level 20, x custom reg, M constr,
  format "''['  M [ x ]  )").
Notation "''[' M ]" := (cond2_ _ M skip_ skip_)
  (in custom cmd at level 20, M constr, only printing,
  format "''[' M ]").
Notation "''(' M ]" := (cond2_ _ M abort_ skip_)
  (in custom cmd at level 20, M constr, only printing,
  format "''(' M ]").
Notation "''[' M )" := (cond2_ _ M skip_ abort_)
  (in custom cmd at level 20, M constr, only printing,
  format "''[' M )").

Notation b0 := (choi2so (dim 'H[msys]_finset.setT)%:R%:M).
Notation setT := finset.setT.
Notation set0 := finset.set0.

Fixpoint cmd_vset u : {set mlab} :=
    match u with
    | skip_       => set0
    | abort_      => set0
    | init_  T x v => mset x
    | circuit_ u  => ucmd_vset u 
    | seqc_ c1 c2 => cmd_vset c1 :|: cmd_vset c2
    | cond_ T F x M f => mset x :|: (\bigcup_i cmd_vset (f i))
    | while_ T x M c => mset x :|: cmd_vset c 
    | nchoice_ c1 c2 => cmd_vset c1 :|: cmd_vset c2
    | pchoice_ p c1 c2 => cmd_vset c1 :|: cmd_vset c2
    end.

Import HermitianTopology.

(* Structural definition of Section 7 *)
Fixpoint fsem_aux (c : cmd_) : set 'SO[msys]_setT :=
  match c with
    | abort_            => [set 0]
    | skip_             => [set \:1]
    | circuit_ u        => [set formso (usem u)]
    | init_ T x v       => [set liftfso (initialso (tv2v x v))]  
    | seqc_ c1 c2       => [set l2 :o l1 | l1 in fsem_aux c1 & l2 in fsem_aux c2]
    | cond_ T F x M fc  => [set f | exists l : F -> 'SO, 
        ifso (liftf_fun (tm2m x x M)) l = f /\ forall i, fsem_aux (fc i) (l i) ]
    | while_ T x M c    => [set f | exists l : nat -> 'SO, 
            whilegso (liftf_fun (tm2m x x M)) l = f /\
               forall n : nat, (fsem_aux c) (l n) ]
    | nchoice_ c1 c2    => fsem_aux c1 `|` fsem_aux c2
    | pchoice_ p c1 c2  => [ set (val p) *: l1 + (1 - val p) *: l2 
                                | l1 in fsem_aux c1 & l2 in fsem_aux c2 ]
  end.

HB.lock Definition fsem := fsem_aux.

(* equivalence of programs *)
HB.lock
Definition eq_fsem u1 u2 := fsem u1 = fsem u2.
Infix "=c" := eq_fsem (at level 70).

Lemma eq_fsem_trans : 
  forall a b c, a =c b -> b =c c -> a =c c.
Proof. by rewrite eq_fsem.unlock; move=>a b c -> ->. Qed.
Lemma eq_fsem_refl : forall a, a =c a.
Proof. by rewrite eq_fsem.unlock. Qed.
Lemma eq_fsem_sym : forall a b, a =c b -> b =c a.
Proof. by rewrite eq_fsem.unlock; move=>a b ->. Qed.
Hint Extern 0 (eq_fsem _ _) => (apply eq_fsem_refl) : core.

Add Parametric Relation : cmd_ eq_fsem
  reflexivity proved by eq_fsem_refl
  symmetry proved by eq_fsem_sym
  transitivity proved by eq_fsem_trans
  as eq_fsem_rel.

(* structural representation *)
Section fsem.
Local Open Scope classical_set_scope.

Lemma fsem_abortE : fsem <{[ abort ]}> = [set 0].
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_skipE : fsem <{[ skip ]}> = [set \:1].
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_initE T (x : qreg T) v :
  fsem <{[ [x] := v ]}> = [set liftfso (initialso (tv2v x v))].
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_circuitE u :
  fsem <{[ [cir u ] ]}> = [set formso (usem u)].
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_seqE c1 c2 :
  fsem <{[ c1 ;; c2 ]}> = [ set l2 :o l1 | l1 in fsem c1 & l2 in fsem c2].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_condE T F x M fc : fsem (@cond_ T F x M fc) = 
  [set f | exists l : F -> 'SO, 
        ifso (liftf_fun (tm2m x x M)) l = f /\ forall i, fsem (fc i) (l i) ].
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_cond2E T x M c0 c1 : fsem (@cond2_ T x M c0 c1) = 
  [set l1 :o formso (liftf_lf (tf2f x x (M true))) + 
       (l0 :o formso (liftf_lf (tf2f x x (M false))))
              | l1 in fsem c1 & l0 in fsem c0].
Proof.
rewrite cond2_.unlock fsem_condE; apply/funext=>i /=; rewrite propeqE fsem.unlock; split.
  move=>[l [ <- Pl]]; exists (l true); first by apply (Pl true).
  exists (l false); first by apply (Pl false).
  by rewrite (ifso_bool true)/= /elemso liftf_funE !tm2mE.
move=>[x1 P1] [x0 P0] <-; exists (fun b => if b then x1 else x0); split; last by case.
by rewrite (ifso_bool true)/= /elemso liftf_funE !tm2mE.
Qed.

Lemma fsem_whileE T x M c : fsem (@while_ T x M c) = 
        [set f | exists l : nat -> 'SO, 
                    whilegso (liftf_fun (tm2m x x M)) l = f /\
                      forall n : nat, (fsem c) (l n) ].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_nchoiceE c1 c2 : fsem <{[ c1 ⊔ c2 ]}> = fsem c1 `|` fsem c2.
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_pchoiceE p c1 c2 : fsem <{[ c1 ⊔_(p) c2 ]}> = 
          [ set (val p) *: l1 + (1 - val p) *: l2 
                                | l1 in fsem c1 & l2 in fsem c2 ].
Proof. by rewrite [fsem]unlock. Qed.

Definition fsemE := (fsem_abortE, fsem_skipE, fsem_initE, fsem_circuitE, 
  fsem_condE, fsem_cond2E, fsem_seqE, fsem_whileE, fsem_nchoiceE, fsem_pchoiceE).

Lemma fsem_pchoiceE1 p c1 c2 :
  fsem <{[ c1 ⊔_(p) c2 ]}> = 
    [ set val p *: i.1 + (1 - val p) *: i.2
      | i in (fsem c1 `*` fsem c2)]%classic.
Proof. by rewrite fsemE image2E; f_equal; apply/funext=>[[a b]]/=. Qed.

Lemma fsem_sequenceE1 c1 c2 :
  fsem <{[ c1 ;; c2 ]}>
    = [ set i.2 :o i.1 | i in (fsem c1 `*` fsem c2)]%classic.
Proof. by rewrite fsemE image2E; f_equal; apply/funext=>[[a b]]/=. Qed.

Lemma fsem_cond2E1 T (x : qreg T) M c1 c0 :
  fsem <{[ c0 ◁ M[x] ▷ c1 ]}> = 
    [ set (i.1 :o formso (liftf_lf (tf2f x x (M true)))) + 
      (i.2 :o formso (liftf_lf (tf2f x x (M false)))) |
        i in (fsem c1 `*` fsem c0)]%classic.
Proof. by rewrite fsemE image2E; f_equal; apply /funext =>[[a b]] /=. Qed.

Lemma fsem_whileE1 T (x : qreg T) M c :
  fsem <{[ M[x] * c ]}> = ((fun l : nat -> 'SO
    => whilegso (liftf_fun (tm2m x x M)) l) @` 
      [ set l : nat -> 'SO | forall n : nat, (fsem c) (l n)])%classic.
Proof.
rewrite fsemE; apply/eq_set=>E; apply/propeqP; split.
move=>[l] [] <- Pl; exists l=>//.
by move=>[l] /= Pl <-; exists l; split.
Qed.

(* the semantics of program is a set of quantum operations *)
Lemma fsem_qo c x : fsem c x -> x \is cptn.
Proof.
elim: c x.
1,2: move=>x; rewrite fsemE/==>->; apply/is_cptn.
by move=>T q v x; rewrite fsemE/==>->; apply/is_cptn.
by move=>u x; rewrite fsemE/==>->; apply/is_cptn.
- move=>c1 IH1 c2 IH2; rewrite fsemE/==>[? [x1 /IH1 P1] [x2 /IH2 P2 <-]].
  by rewrite (QOperation_BuildE P1) (QOperation_BuildE P2) is_cptn.
- move=>T x F M c IH y; rewrite fsemE/==>[[l []]] <- Pi.
  change l with (fun i => l i).
  under eq_fun do rewrite (QOperation_BuildE (IH _ _ (Pi _))).
  by apply/is_cptn.
- move=>T x P c IH f; rewrite fsem_whileE1/= whilegso.unlock=>[[l Pl <-]].
  apply: whilegso_cptn; last by move=>i; apply/IH.
  rewrite -!liftf_lf_adj -!liftf_lf_comp -linearD/= -liftf_lf_le1.
  move: (@is_trnincr _ _ _ (tm2m x x P)).
  by rewrite /trace_nincr big_bool/= !tm2mE addrC.
- by move=>c1 IH1 c2 IH2 x; rewrite fsemE/==>[[/IH1|/IH2]].
- move=>[] s Ps c1 + c2 + f; rewrite fsemE/==>++ [x1 P1] [x2 P2] <-.
  move=>/(_ _ P1) IH1 /(_ _ P2) IH2; apply/cptnP; split.
  rewrite -geso0_cpE addv_ge0// scalev_ge0// ?subr_ge0 ?geso0_cpE.
  1,3: by move: Ps=>/andP[]. 1,2: by apply/cptn_cpmap.
  apply/tnmapP=>x; rewrite !soE linearD/= !linearZ/= -[\Tr x]mul1r 
    -{2}[1](subrK s) addrC [_ * \Tr x]mulrDl lerD// ler_wpM2l ?subr_ge0//.
  1,3: by move: Ps=>/andP[]. 1,2: by apply/tnmapP/cptn_tnmap.
Qed.
Canonical fsem_cpType c x {H : fsem c x} :=
  @CPMap_Build _ _ x (cptn_cpmap (fsem_qo H)).
Canonical fsem_qoType c x {H : fsem c x} :=
  @QOperation_Build _ _ x (fsem_qo H).

(* the semantics of program is non-empty set *)
Lemma fsem_nonempty c : (fsem c !=set0)%classic.
Proof.
elim: c=>[ | | T x v | u | | | | | ].
by rewrite fsemE; exists \:1.
by rewrite fsemE; exists 0.
by rewrite fsemE; exists (liftfso (initialso (tv2v x v))).
by rewrite fsemE; exists (formso (usem u)).
- move=>c1 [x1 P1] c2 [x2 P2]; exists (x2 :o x1); 
  by rewrite fsemE/=; exists x1=>//; exists x2.
- move=>T F x M c IH; exists (ifso (liftf_fun (tm2m x x M)) (fun i => projT1 (cid (IH i)))).
  rewrite fsemE/=; exists (fun i => projT1 (cid (IH i))); split=>// i; apply: projT2.
- move=>T x M c [y Py].
  exists (whilegso (liftf_fun (tm2m x x M)) (fun=>y)).
  rewrite fsemE/=; exists (fun =>y)=>//.
- by move=>c1 [x1 P1] c2 _; exists x1; rewrite fsemE/=; left.
- move=>s c1 [x1 P1] c2 [x2 P2].
  exists (val s *: x1 + (1 - val s) *: x2).
  by rewrite fsemE/=; exists x1=>//; exists x2.
Qed.

(* the semantics of a program can be formulated locally, *)
(* i.e., x in fsem c -> x = E ⊗ I for some local quantum operation E *)
Lemma fsem_local c x : fsem c x -> exists E : 'SO_(cmd_vset c), x = liftfso E.
Proof.
move: finset.subsetUl finset.subsetUr=>/(_ mlab) Ul /(_ mlab) Ur.
elim: c x.
by move=>x; rewrite fsemE/==>->; exists \:1; rewrite liftfso1.
by move=>x; rewrite fsemE/==>->; exists 0; rewrite linear0.
by move=>T x v y; rewrite fsemE/==>->; exists (initialso (tv2v x v)).
- move=>u x; rewrite fsemE/==>->; move: (usem_local u)=>[U PU]; 
  by exists (formso U); rewrite PU liftfso_formso.
- move=>c1 IH1 c2 IH2 x; rewrite fsemE/==>[[x1 /IH1 [E1 ->]] [x2 /IH2 [E2 ->]] <-].
  exists (liftso (finset.subsetUr _ _) E2 :o liftso (finset.subsetUl _ _) E1).
  by rewrite liftfso_comp !liftfso2.
- move=>T F x M c IH y; rewrite fsemE/==>[[l [P Pl]]].
  pose ci i : 'SO_(\bigcup_i cmd_vset (c i)) := 
    liftso (finset.bigcup_sup i is_true_true) (projT1 (cid (IH _ _ (Pl i)))).
  have P3i i : l i = liftfso (ci i)
    by rewrite /ci liftfso2; move: (projT2 (cid (IH _ _ (Pl i)))).
  exists (ifso (lift_fun (finset.subsetUl _ _) (tm2m x x M)) 
      (fun i : F => liftso (finset.subsetUr _ _) (ci i))).
  rewrite liftfso_ifso liftf_fun2.
  by under [in RHS]eq_fun do rewrite liftfso2 -P3i.
- move=>T x M c + ?; rewrite fsemE whilegso.unlock/==>[IH [f [] ] <- Pf].
  pose g i := liftso (Ur (mset x) _) (projT1 (cid (IH _ (Pf i)))).
  have Pg i : f i = liftfso (g i).
    by move: (projT2 (cid (IH _ (Pf i))))=>->; rewrite /g liftfso2.
  exists (limn (fun n => \sum_(i < n) (formso (lift_lf (Ul _ _) (tf2f x x (M false))) :o 
    (\compr_(j < i) (g j :o formso (lift_lf (Ul _ _) (tf2f x x (M true)))))))).
  rewrite -[RHS]extnum.linear_lim.
    apply: whilegso_is_cvgn; last first.
      by move=>i; rewrite -liftfso_qoE -Pg; apply: (@fsem_qo c).
    rewrite -!lift_lf_adj -!lift_lf_comp -linearD/= -lift_lf_le1.
    move: (@is_trnincr _ _ _ (tm2m x x M)).
    by rewrite /trace_nincr big_bool/= !tm2mE addrC.
  apply: eq_lim=>i/=; rewrite linear_sum; apply eq_bigr=>j _ /=.
  rewrite !liftfso_comp; f_equal.
    by rewrite liftfso_formso liftf_lf2 liftf_funE tm2mE.
  elim/big_rec2: _ =>[|k y1 ? _ ->]; first by rewrite liftfso1.
  by rewrite !liftfso_comp -liftso_formso liftfso2 
    comp_soErl -Pg liftf_funE tm2mE liftfso_formso.
- move=>c1 IH1 c2 IH2 x; rewrite fsemE/==>[[/IH1[E ->]|/IH2[E ->]]].
  by exists (liftso (Ul _ _) E); rewrite liftfso2.
  by exists (liftso (Ur _ _) E); rewrite liftfso2.
- move=>[] p Pp c1 IH1 c2 IH2 ?; rewrite fsemE/==>[[?/IH1 [E1 ->]][?/IH2 [E2 ->]]<-].
  exists ((liftso (Ul _ _) (p *: E1)) + (liftso (Ur _ _) ((1-p) *: E2))).
  by rewrite linearD/= !linearZ/= !liftfso2.
Qed.

(* if c does not contain nondeterministic choice ⊔, then its semantics  *)
(*   is deterministic, i.e., fsem is a set of only one element          *)
Lemma fsem_no_nchoice (c : cmd_) :
  no_nchoice_ c -> exists x, fsem c = [set x].
Proof.
elim: c; rewrite /= ?fsemE.
by exists \:1.
by exists 0.
by move=>T x v; exists (liftfso (initialso (tv2v x v))); rewrite fsemE.
by move=>u; exists (formso (usem u)); rewrite fsemE.
- move=>c1 IH1 c2 IH2 /andP[] /IH1 [x1 P1] /IH2 [x2 P2].
  by exists (x2 :o x1); rewrite fsemE P1 P2 image2_set1.
- move=>T F x M c IH /forallP Pi.
  exists (ifso (liftf_fun (tm2m x x M)) (fun i => projT1 (cid (IH i (Pi i))))).
  rewrite fsemE; apply/eq_set=>y; apply/propeqP; split.
    move=>[l][]<- Pl; f_equal; apply/funext=>i;
    move: (IH i (Pi i)) (IH i (Pi i)) (Pl i)=>[y0 ->]/= PH ->.
    move: (projT2 (cid PH)); apply: eq_set1.
  move=>->; exists (fun i : F => projT1 (cid (IH i (Pi i)))); split=>// i.
  by move: (projT2 (cid (IH i (Pi i))))=>{1}->.
- move=>T x M c IH /IH [y0 P].
  exists (whilegso (liftf_fun (tm2m x x M)) (fun=> y0)).
  rewrite fsemE; apply/eq_set=>y; apply/propeqP; split.
    by move=>[l][]<- Pl; f_equal; apply/funext=>i; move: (Pl i); rewrite P.
  by move=>->; exists (fun=>y0); split=>// i; rewrite P.
- by [].
- move=>p c1 IH1 c2 IH2 /andP[] /IH1 [x1 P1] /IH2 [x2 P2].
  by exists (val p *: x1 + (1 - val p) *: x2); rewrite fsemE P1 P2 image2_set1.
Qed.

(* syntactically calculate if quantum register x is disjoint from the program c *)
Fixpoint cmd_var_disj T (x : qreg T) (c : cmd_) :=
    match c with
    | skip_ | abort_ => true
    | init_ _ y _ => disjoint_qreg x y
    | circuit_ u => ucmd_var_disj x u
    | cond_ _ F y _ f => disjoint_qreg x y && [forall i : F, cmd_var_disj x (f i)]
    | while_ _ y _ c => disjoint_qreg x y && cmd_var_disj x c
    | seqc_ c1 c2 | nchoice_ c1 c2 | pchoice_ _ c1 c2 => 
        cmd_var_disj x c1 && cmd_var_disj x c2 
    end.

(* x is syntactical disjoint from c -> the quantum systems of x and c are disjoint *)
Lemma cmd_var_disjP T (x : qreg T) (c : cmd_) :
    cmd_var_disj x c -> [disjoint mset x & cmd_vset c]%B.
Proof.
elim: c=>/=.
1,2: by rewrite disjointX0.
by move=>???; rewrite -disj_setE.
by move=>? /ucmd_var_disj_vsetP.
by move=>? IH1 ? IH2 /andP[] /IH1 + /IH2; rewrite disjointXU=>->->.
- move=>? ? y ? fu IH /andP[] + /forallP Pi.
  rewrite disjointXU -disj_setE=>-> /=.
  by apply/bigcup_disjoint=>i _; apply/IH/Pi.
- move=>? y ? ? IH /andP[] + /IH.
  by rewrite disjointXU -disj_setE=>->->.
- by move=>? IH1 ? IH2 /andP[] /IH1 + /IH2; rewrite disjointXU=>->->.
- by move=>?? IH1 ? IH2 /andP[] /IH1 + /IH2; rewrite disjointXU=>->->.
Qed.

(* syntactically calculate if a circuit u is disjoint from the program c *)
Fixpoint cmd_ucmd_disj (u : ucmd_) (c : cmd_) :=
    match u with
    | uskip_ => true
    | unitary_ _ y _ => cmd_var_disj y c 
    | sequ_ u1 u2 => cmd_ucmd_disj u1 c && cmd_ucmd_disj u2 c 
    | qcond_ _ F y _ fu => cmd_var_disj y c && [forall i : F, cmd_ucmd_disj (fu i) c]
    end.

(* u is syntactical disjoint from c -> the quantum systems of u and c are disjoint *)
Lemma cmd_ucmd_disjP u c :
  cmd_ucmd_disj u c -> [disjoint ucmd_vset u  & cmd_vset c]%B.
Proof.
elim: u.
by rewrite /= disjoint0X.
by move=>???/=/cmd_var_disjP.
by move=>u1 IH1 u2 IH2/=/andP[] /IH1 + /IH2; rewrite disjointUX=>->->.
move=>?? x ? f IH /=/andP[]/cmd_var_disjP + /forallP Pi.
rewrite disjointUX=>->/=; rewrite disjoint_sym; apply/bigcup_disjoint=>i _.
by rewrite disjoint_sym; apply/IH/Pi.
Qed.

(* syntactically calculate if two programs are disjoint *)
Fixpoint cmd_disj c1 c2 :=
    match c1 with
    | skip_ | abort_     => true
    | init_ _ x _ => cmd_var_disj x c2
    | circuit_ u  => cmd_ucmd_disj u c2
    | seqc_ c11 c12 | nchoice_ c11 c12 | pchoice_ _ c11 c12 => 
        cmd_disj c11 c2 && cmd_disj c12 c2
    | cond_ _ _ x _ f => cmd_var_disj x c2 && [forall i, cmd_disj (f i) c2]
    | while_ _ x _ c1 => cmd_var_disj x c2 && cmd_disj c1 c2
    end.

(* disjoint programs acts on disjoint systems *)
Lemma cmd_disjP c1 c2 :
    cmd_disj c1 c2 -> [disjoint cmd_vset c1 & cmd_vset c2]%B.
Proof.
elim: c1.
1,2: by rewrite /= disjoint0X.
by move=>???/=/cmd_var_disjP.
by move=>?/=/cmd_ucmd_disjP.
by move=>? IH1 ? IH2/=/andP[]/IH1+/IH2; rewrite disjointUX=>->->.
move=>????? IH/=/andP[]/cmd_var_disjP+/forallP Pi.
rewrite disjointUX=>->/=; rewrite disjoint_sym bigcup_disjoint// =>i _;
by rewrite disjoint_sym IH.
by move=>????/= IH/andP[]/cmd_var_disjP+/IH; rewrite disjointUX=>->->.
by move=>? IH1 ? IH2/=/andP[]/IH1+/IH2; rewrite disjointUX=>->->.
by move=>?? IH1 ? IH2/=/andP[]/IH1+/IH2; rewrite disjointUX=>->->.
Qed.

End fsem.

Module Export EQ_FSEM.
Require Import Setoid.

Add Parametric Morphism (T : qType) : (@init_ T )
  with signature (@eq_qreg T) ==> (@eq _) ==> eq_fsem as eq_fsem_init.
Proof.
move=>x y Pxy U; rewrite eq_fsem.unlock !fsemE -(tv2v_eqr _ Pxy).
by move: (mset_eqr default_qmemory Pxy)=>P; case: _ / P; rewrite casths_id.
Qed.

(*---------------------------------------------------------------------------*)
(*                     Lemma 5.1 (Congruence - Lifting law)                  *)
(* It is states as a relation morphism, and this allows to directly rewrite  *)
(*                 [cir u]  ==>  [cir u']    if   u =u u'                    *)
(* and thus allows to substitut in all composition of circuit in qwhile      *)
(*---------------------------------------------------------------------------*)
Add Parametric Morphism : circuit_
  with signature eq_usem ==> eq_fsem as eq_fsem_circuit.
Proof. by move=>x y; rewrite eq_fsem.unlock !fsemE eq_usem.unlock=>->. Qed.

Add Parametric Morphism : seqc_
  with signature eq_fsem ==> eq_fsem ==> eq_fsem as eq_fsem_seqc.
Proof. by rewrite eq_fsem.unlock=>??+??+; rewrite !fsemE=>->->. Qed.

Add Parametric Morphism (T : qType) (F : finType) : (@cond_ T F)
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq _) ==> eq_fsem as eq_fsem_cond.
Proof.
move=>x y Pxy M f; rewrite eq_fsem.unlock !fsemE.
suff ->: (liftf_fun (tm2m x x M)) = (liftf_fun (tm2m y y M)) by [].
by apply/funext=>i; rewrite !liftf_funE !tm2mE -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Add Parametric Morphism T : (@cond2_ T)
  with signature (@eq_qreg T) ==> (@eq _) ==> eq_fsem ==> eq_fsem ==> eq_fsem
    as eq_fsem_cond2.
Proof.
move=>x y Pxy M c00 c01 + c10 c11 +.
by rewrite eq_fsem.unlock !fsemE -!(tf2f_eqr _ Pxy Pxy) !liftf_lf_cast=>->->.
Qed.

Add Parametric Morphism (T : qType) : (@while_ T)
  with signature (@eq_qreg T) ==> (@eq _) ==> eq_fsem ==> eq_fsem
    as eq_fsem_while.
Proof.
move=>x y Pxy M c1 c2; rewrite eq_fsem.unlock !fsemE=>->.
suff ->: (liftf_fun (tm2m x x M)) = (liftf_fun (tm2m y y M)) by [].
by apply/funext=>i; rewrite !liftf_funE !tm2mE -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Add Parametric Morphism : nchoice_
  with signature eq_fsem ==> eq_fsem ==> eq_fsem as eq_fsem_nchoice.
Proof. by rewrite eq_fsem.unlock=>??+??+; rewrite !fsemE=>->->. Qed.

Add Parametric Morphism p : (pchoice_ p)
  with signature eq_fsem ==> eq_fsem ==> eq_fsem as eq_fsem_pchoice.
Proof. by rewrite eq_fsem.unlock=>??+??+; rewrite !fsemE=>->->. Qed.

Lemma uskip_skip : <{[ [cir uskip] ]}> =c <{[ skip ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE/= !usemE formso1. Qed.

Lemma eq_cond (T : qType) (x : qreg T) (F : finType) (M1 M2 : 'QM(F; 'Ht T))
  (f1 f2 : F -> cmd_) :
  (forall i, M1 i = M2 i) -> (forall i, f1 i =c f2 i) -> 
    cond_ x M1 f1 =c cond_ x M2 f2.
Proof.
rewrite eq_fsem.unlock=>PM Pf; rewrite !fsemE.
apply/eq_set=>y; apply/propeqP; split; move=>[l [ <- P2]]; exists l; 
(split; [ f_equal; apply/funext=>i; rewrite !liftf_funE !tm2mE PM// |
  move=>i; move: (Pf i); try do [move=>->//|move=><-//] ]).
Qed.

Lemma eq_condl (T : qType) (x : qreg T) (F : finType) (M1 M2 : 'QM(F; 'Ht T))
  (f: F -> cmd_) :
  (forall i, M1 i = M2 i) -> cond_ x M1 f =c cond_ x M2 f.
Proof. by move=>/eq_cond; apply. Qed.

Lemma eq_condr (T : qType) (x : qreg T) (F : finType) (M : 'QM(F; 'Ht T))
  (f1 f2 : F -> cmd_) :
  (forall i, f1 i =c f2 i) -> cond_ x M f1 =c cond_ x M f2.
Proof. by move=>/eq_cond; apply. Qed.

Lemma eq_cond2 T (x : qreg T) (M1 M2 : 'QM) c0 c1 :
  (forall i, M1 i = M2 i) -> cond2_ x M1 c0 c1 =c cond2_ x M2 c0 c1.
Proof. by rewrite cond2_.unlock; exact: eq_condl. Qed.

Lemma seqc_circuit u1 u2 :
  <{[ [cir u1 ; u2 ] ]}> =c <{[ ([cir u1 ]) ;; ([cir u2 ]) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE usemE; apply/eq_set=>i /=; apply/propeqP; split.
by move=>->; exists (formso (usem u1))=>//; 
  exists (formso (usem u2))=>//; rewrite formso_comp.
by move=>[?->][?->]<-; rewrite formso_comp.
Qed.

Lemma eq_init (T : qType) (x : qreg T) (v1 v2 : 'NS('Ht T)) :
  v1 = v2 :> 'Ht T -> <{[ [x] := v1 ]}> =c <{[ [x] := v2 ]}>.
Proof. by move=>Pv; rewrite eq_fsem.unlock !fsemE/= Pv. Qed.

Lemma eq_while (T : qType) (x : qreg T) (M1 M2 : 'QM) c :
  (forall i, M1 i = M2 i) -> <{[ M1[x] * c ]}> =c <{[ M2[x] * c ]}>.
Proof.
move=>P; rewrite eq_fsem.unlock !fsemE.
suff ->: (liftf_fun (tm2m x x M1)) = (liftf_fun (tm2m x x M2)) by [].
by apply/funext=>i; rewrite !liftf_funE !tm2mE P.
Qed.

Lemma eq_seqcl u1 u2 u3 :
  u1 =c u2 -> <{[ u1 ;; u3 ]}> =c <{[ u2 ;; u3 ]}>.
Proof. by move=>->. Qed.

Lemma eq_seqcr u1 u2 u3 :
  u1 =c u2 -> <{[ u3 ;; u1 ]}> =c <{[ u3 ;; u1 ]}>.
Proof. by move=>->. Qed.

Lemma eq_seqc u1 u2 u3 u4 :
  u1 =c u2 -> u3 =c u4 -> <{[ u1 ;; u3 ]}> =c <{[ u2 ;; u4 ]}>.
Proof. by move=>->->. Qed.

Lemma eq_nchoicel u1 u2 u3 :
  u1 =c u2 -> <{[ u1 ⊔ u3 ]}> =c <{[ u2 ⊔ u3 ]}>.
Proof. by move=>->. Qed.

Lemma eq_nchoicer u1 u2 u3 :
  u1 =c u2 -> <{[ u3 ⊔ u1 ]}> =c <{[ u3 ⊔ u1 ]}>.
Proof. by move=>->. Qed.

Lemma eq_nchoice u1 u2 u3 u4 :
  u1 =c u2 -> u3 =c u4 -> <{[ u1 ⊔ u3 ]}> =c <{[ u2 ⊔ u4 ]}>.
Proof. by move=>->->. Qed.

Lemma eq_pchoicel p u1 u2 u3 :
  u1 =c u2 -> <{[ u1 ⊔_(p) u3 ]}> =c <{[ u2 ⊔_(p) u3 ]}>.
Proof. by move=>->. Qed.

Lemma eq_pchoicer p u1 u2 u3 :
  u1 =c u2 -> <{[ u3 ⊔_(p) u1 ]}> =c <{[ u3 ⊔_(p) u1 ]}>.
Proof. by move=>->. Qed.

Lemma eq_pchoicep p1 p2 u1 u2 :
  val p1 = val p2 -> <{[ u1 ⊔_(p1) u2 ]}> =c <{[ u1 ⊔_(p2) u2 ]}>.
Proof. by move=>/val_inj->. Qed.

Lemma eq_pchoice p1 p2 u1 u2 u3 u4 :
  val p1 = val p2 -> u1 =c u2 -> u3 =c u4 -> 
    <{[ u1 ⊔_(p1) u3 ]}> =c <{[ u2 ⊔_(p2) u4 ]}>.
Proof. by move=>/val_inj->->->. Qed.

End EQ_FSEM.

Section NonDeterministicLaws.

(* proposition 5.1 (1) : initialization law, cancellation *)
Lemma init_seqcK T (x : 'QReg[T]) (phi psi : 'NS('Ht T)) :
  <{[ ([x] := phi) ;; ([x] := psi) ]}> =c <{[ [x] := psi ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE image2_set1; f_equal.
rewrite -liftfso_comp; f_equal; apply/superopP =>y;
by rewrite soE !initialsoE linearZ/= outp_trlf tv2v_dot ns_dot mulr1.
Qed.

(* proposition 5.1 (2) : initialization law, unitary-elimination *)
Lemma init_circuitK T (x : 'QReg[T]) phi (u : ucmd_) (sc : 'FU('Ht T)) :
  usem u = liftf_lf (tf2f x x sc) -> 
  <{[ ([x] := phi) ;; ([cir u ]) ]}> =c
    <{[ [x] := [NS of sc (phi : 'Ht T)] ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE image2_set1=>->; f_equal.
rewrite -liftfso_formso -liftfso_comp;
by f_equal; apply/superopP =>y; rewrite soE !initialsoE formsoE 
  linearZr/= linearZl/= outp_compr outp_compl adjfK tf2f_apply.
Qed.

Lemma init_unitaryK T (x : 'QReg[T]) phi (u : 'FU('Ht T)) :
    <{[ ([x] := phi) ;; ([cir [x] *= u ]) ]}> =c 
      <{[ [x] := [NS of u (phi : 'Ht T)] ]}>.
Proof. by rewrite -(init_circuitK _ (u := <{[ [x] *= u ]}>))// usemE. Qed.

Lemma init_unitaryKP T (x : 'QReg[T]) (phi v : 'NS) (u : 'FU('Ht T)) :
v = u (phi : 'Ht T) :> 'Ht T ->
  <{[ ([x] := phi) ;; ([cir [x] *= u ]) ]}> =c <{[ [x] := v ]}>.
Proof. by move=>P; rewrite init_unitaryK; apply eq_init. Qed.

(* proposition 5.1 (3) : initialization law, qif-elimination *)
Lemma init_qifTK (x : qreg Bool) (psi : 'NS('Ht Bool)) 
  (phi : 'ONB(bool; 'Ht Bool)) c0 c1 {H : `{{ucmd_var_disj x c1}}} :
  [< (psi : 'Ht _) ; phi false >] = 0 ->
  <{[ ([x] := psi) ;; ([cir c0 ← phi[x] → c1 ]) ]}> =c
    <{[ ([x] := phi true) ;; ([cir c1 ]) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE usemE !image2_set1=>P1; f_equal.
apply/superopP=>y; rewrite !soE.
set phi1 := liftf_lf _. set phi0 := liftf_lf _.
have ->: phi1 \o usem c1 = usem c1 \o phi1.
  by move: (usem_local c1)=>[U ->]; rewrite liftf_lf_compC// ucmd_var_disj_vsetP.
rewrite -[_ \o phi1]comp_lfunA.
have ->: phi1 \o phi1 = phi1
  by rewrite -liftf_lf_comp tf2f_comp outp_comp onb_dot eqxx scale1r.
rewrite !comp_lfunDl adjfD !comp_lfunDr !adjf_comp !comp_lfunA.
have -> : phi1^A = phi1 by rewrite -liftf_lf_adj tf2f_adj adj_outp.
have -> : phi0^A = phi0 by rewrite -liftf_lf_adj tf2f_adj adj_outp.
have P2 : forall A : 'F[msys]_setT, A \o liftfso (initialso (tv2v x psi)) y \o phi0 = 0.
  move=>A; rewrite liftfso_krausso kraussoE/= -comp_lfunA linear_suml/= big1 ?comp_lfun0r// =>i _.
  by rewrite liftf_funE -liftf_lf_adj -!comp_lfunA -liftf_lf_comp 
    adj_outp -tv2v_out outp_comp tv2v_dot P1 scale0r linear0 !comp_lfun0r.
rewrite !P2 !comp_lfun0l !addr0 -[RHS]addr0; f_equal.
f_equal; rewrite -!comp_lfunA; f_equal; rewrite !liftfso_krausso 
  !kraussoE linear_suml linear_sumr; apply eq_bigr=>i _ /=.
rewrite !liftf_funE -!liftf_lf_adj !adj_outp !comp_lfunA -comp_lfunA -!liftf_lf_comp -!tv2v_out
  !outp_comp !tv2v_dot !(linearZ, linearZl, linearZr)/= scalerA -[RHS]scale1r.
  f_equal. rewrite -(ns_dot psi).
  by rewrite {3}(onb_vec phi psi) big_bool/= dotpDl !dotpZl/= !conj_dotp P1 mul0r addr0 mulrC.
rewrite [X in X \o _]comp_lfunACA.
set t1 := _ \o liftfso _ _; have ->: t1 = 0.
rewrite /t1 liftfso_krausso kraussoE linear_sumr/= big1// =>i _.
  by rewrite liftf_funE !comp_lfunA -liftf_lf_comp -tv2v_out 
    outp_comp tv2v_dot -conj_dotp P1 conjC0 scale0r linear0 !comp_lfun0l.
by rewrite comp_lfun0r !comp_lfun0l.
Qed.

Lemma init_qifTK1 (x : qreg Bool) (psi : 'NS('Ht Bool)) 
  (phi : 'ONB(bool; 'Ht Bool)) c0 c1 {H : `{{ucmd_var_disj x c1}}} :
  [< (psi : 'Ht _) ; phi false >] = 0 ->
    <{[ ([x] := psi) ;; ([cir c0 ← phi[x] → c1 ]) ]}> =c 
      <{[ ([x] := psi) ;; ([cir c1 ]) ]}>.
Proof.
move=>P; rewrite init_qifTK//; apply eq_seqcl.
rewrite eq_fsem.unlock !fsemE; do 2 f_equal; apply/superopP=>r.
rewrite !initialsoE; f_equal; rewrite !tv2v_out; f_equal.
move: (onb_vec phi psi); rewrite big_bool/= -[[< phi false; _>]]conj_dotp P conjC0 scale0r addr0=>P1.
move: {+}P1=>/(f_equal normr); rewrite normrZ !ns_norm mulr1=>P2.
by rewrite P1 outpZl outpZr scalerA -normCK -P2 expr1n scale1r.
Qed.

Lemma init_qifFK (x : qreg Bool) (psi : 'NS('Ht Bool)) 
  (phi : 'ONB(bool; 'Ht Bool)) c0 c1 {H : `{{ucmd_var_disj x c0}}} :
  [< (psi : 'Ht _) ; phi true >] = 0 ->
    <{[ ([x] := psi) ;; ([cir c0 ← phi[x] → c1 ]) ]}> =c
      <{[ ([x] := phi false) ;; ([cir c0 ]) ]}>.
Proof.
move=>P; rewrite qif_sym init_qifTK//=.
suff ->: (init_ x ([ONB of onb_swap phi] true)) =c (init_ x (phi false)) by [].
by apply eq_init=>/=.
Qed.

(* proposition 5.1 (4) : initialization law, if-elimination *)
Lemma init_ifTK T (x : 'QReg[T]) (psi : 'NS('Ht T)) c0 c1 :
  <{[ ([x] := psi) ;; (c0 ◁ '[| psi >][x] ▷ c1) ]}> =c 
    <{[ ([x] := psi) ;; c1 ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE/= !image2_set1; apply/eq_set=>?/=; apply/propeqP; split.
move=>[?][x1 P1][x0 P0]<-<-; exists x1=>//; symmetry.
2: move: (fsem_nonempty c0)=>[x0 P0][x1 P1]<-;
  exists (x1 :o formso (liftf_lf (tf2f x x [> psi; psi <])) +
    (x0 :o formso (liftf_lf (tf2f x x (\1 - [> psi; psi <])))));
  first by exists x1=>//; exists x0=>//.
all: rewrite linearDl/= -!comp_soA -!liftfso_formso -!liftfso_comp -[RHS]addr0; do ! f_equal.
1,3: apply/superopP=>y; rewrite soE initialsoE formsoE linearZr/= linearZl/=; f_equal;
by rewrite tf2f_adj adj_outp tv2v_out !tf2f_comp outp_comp ns_dot scale1r outp_comp ns_dot scale1r.
all: set t := formso _ :o _; suff ->: t = 0 by rewrite linear0 comp_so0r.
all: by apply/superopP=>y; rewrite /t soE initialsoE !soE linearZr/= tv2v_out tf2f_comp 
  linearBl/= outp_comp ns_dot scale1r comp_lfun1l subrr linear0 scaler0 comp_lfun0l.
Qed.

Lemma init_ifFK (x : qreg Bool) (phi psi : 'NS('Ht Bool)) c0 c1 :
  [< (phi : 'Ht _); (psi : 'Ht _) >] = 0 ->
    <{[ ([x] := phi) ;; (c0 ◁ '[| psi >][x] ▷ c1) ]}> =c 
      <{[ ([x] := phi) ;; c0 ]}>.
Proof.
move=>P; rewrite eq_fsem.unlock !fsemE !image2_set1; apply/eq_set=>?/=; apply/propeqP; split.
move=>[?][x1 P1][x0 P0]<-<-; exists x0=>//; symmetry.
2: move: (fsem_nonempty c1)=>[x1 P1] [x0 P0]<-;
  exists (x1 :o formso (liftf_lf (tf2f x x [> psi; psi <])) +
    (x0 :o formso (liftf_lf (tf2f x x (\1 - [> psi; psi <])))));
  first by exists x1=>//; exists x0.
all: rewrite linearDl/= -!comp_soA -!liftfso_formso 
  -!liftfso_comp -[RHS]add0r; do ! f_equal.
1,3: set t := formso _ :o _; suff ->: t = 0 by rewrite linear0 comp_so0r.
1,2: by apply/superopP=>y; rewrite /t soE initialsoE !soE linearZr/= tv2v_out
  tf2f_comp outp_comp -conj_dotp P conjC0 scale0r linear0 scaler0 comp_lfun0l.
all: apply/superopP=>y; rewrite soE initialsoE formsoE linearZr/= linearZl/=; f_equal.
all: by rewrite tf2f_adj adjfB adjf1 adj_outp -!tf2fB tf2f1 tv2v_out linearBl/= 
  tf2f_comp outp_comp -conj_dotp P conjC0 scale0r tf2f0 subr0 comp_lfun1l 
  linearBr/= tf2f_comp outp_comp P scale0r tf2f0 subr0 comp_lfun1r.
Qed.

(* proposition 5.1 (5) : if Expansion *)
(* for simplicity, we focus on the simple case of r, i.e., r = (q1, q2) *)
(*   other type structures are in principle the same *)
Lemma if_expansion T1 T2 (x1 : 'QReg[T1]) (x2 : 'QReg[T2]) 
  (P : evalQT T1 -> cmd_) (phi : 'NS('Ht (T1 * T2))) {Hx : `{{disjoint_qreg x1 x2}}}
  {H : `{{forall i, cmd_var_disj <{(x1,x2)}> (P i)}}} 
  {HP : `{{forall i, no_nchoice_ (P i)}}} :
    <{[ If tmeas[x1] = m then P m fI ;; [(x1,x2)] := phi ]}> =c
      <{[ If tmeas[(x1,x2)] = k then P k.1 fI ;; [(x1,x2)] := phi ]}>.
Proof.
move: Hx; rewrite /cmd_expose=>Hx.
rewrite eq_fsem.unlock !fsemE !image2_set1; apply/eq_set=>?/=; apply/propeqP; split.
- move=>[?[f][ <-]P1 <-].
  exists (ifso (liftf_fun (tm2m <{ (x1, x2) }> <{ (x1, x2) }> tmeas)) 
    (fun i : evalQT (T1 * T2) => f i.1)).
  exists (fun i : evalQT (T1 * T2) => f i.1)=>//.
  rewrite !ifso_elem pair_bigV/= !linear_sumr/=.
  apply eq_bigr; rewrite -/evalQT=>i _.
  rewrite -linear_sumr/= !comp_soA.
  move: (fsem_local (P1 i))=>[E ->]; rewrite liftfso_compC ?cmd_var_disjP//.
  rewrite -!comp_soA; f_equal.
  transitivity (liftfso (initialso (tv2v <{(x1, x2)}> phi)) :o 
    formso (liftf_lf (tf2f  <{(x1, x2)}> <{(x1, x2)}> ([> ''i ; '' i <] ⊗f \1))));
  last by rewrite /elemso liftf_funE -tf2f_pair liftf_lf_cast tf2f1 liftf_lf_tenf1r -?disj_setE.
  under eq_bigr do rewrite /elemso liftf_funE -liftfso_formso.
  rewrite -linear_sum/= -liftfso_formso -!liftfso_comp; f_equal.
  rewrite -(initialso_onb (tv2v <{ (x1, x2) }> phi) (tv2v_fun _ <{ (x1, x2) }> t2tv)).
  rewrite -elemso_sum !linear_suml/=; apply eq_bigr=>[[j1 j2]] _.
  rewrite /elemso linear_sumr/= (bigD1 j2)//= big1=>[k /negPf nkj|];
  rewrite !formso_comp tm2mE tmeasE /tv2v_fun tv2v_out !tf2f_comp outp_comp.
  by rewrite -!tentv_t2tv tentv_dot !t2tv_dot [_ == k]eq_sym nkj mulr0 scale0r tf2f0 formso0.
  rewrite addr0; do 2 f_equal.
  rewrite -(sumonb_out t2tv) tentf_sumr linear_sumr/= (bigD1 j2)//= big1=>[k /negPf nkj|];
  by rewrite tentv_out ?addr0 outp_comp -!tentv_t2tv// 
    tentv_dot !t2tv_dot [_ == k]eq_sym nkj mulr0 scale0r.
move=>[?[f][ <-]P1 <-].
exists (ifso (liftf_fun (tm2m x1 x1 tmeas))
(fun i : evalQT T1 => f (i,witness _))).
exists (fun i : evalQT T1 => f (i, witness (evalQT T2))); split=>// i.
by move: (P1 (i, witness (evalQT T2))).
have Pij: forall i j, f (i, j) = f (i, witness (evalQT T2)).
  move=>i j; move: (fsem_no_nchoice (HP i))=>[E PE].
  by move: (P1 (i,j)) (P1 (i, witness _))=>/=; rewrite PE/==>->->.
rewrite !ifso_elem pair_bigV/= !linear_sumr/=.
apply eq_bigr; rewrite -/evalQT=>i _.
under eq_bigr do rewrite Pij.
rewrite -linear_sumr/= !comp_soA.
move: (fsem_local (P1 (i,witness _)))=>[/= E ->]; rewrite liftfso_compC ?cmd_var_disjP//.
rewrite -!comp_soA; f_equal.
transitivity (liftfso (initialso (tv2v <{(x1, x2)}> phi)) :o 
  formso (liftf_lf (tf2f  <{(x1, x2)}> <{(x1, x2)}> ([> ''i ; '' i <] ⊗f \1)))).
by rewrite /elemso liftf_funE -tf2f_pair liftf_lf_cast tf2f1 liftf_lf_tenf1r -?disj_setE.
under eq_bigr do rewrite /elemso liftf_funE -liftfso_formso.
rewrite -linear_sum/= -liftfso_formso -!liftfso_comp; f_equal.
rewrite -(initialso_onb (tv2v <{ (x1, x2) }> phi) (tv2v_fun _ <{ (x1, x2) }> t2tv)).
rewrite -elemso_sum !linear_suml/=; apply eq_bigr=>[[j1 j2]] _.
rewrite /elemso linear_sumr/= (bigD1 j2)//= big1=>[k /negPf nkj|];
rewrite !formso_comp tm2mE tmeasE /tv2v_fun tv2v_out !tf2f_comp outp_comp.
by rewrite -!tentv_t2tv tentv_dot !t2tv_dot [_ == k]eq_sym nkj mulr0 scale0r tf2f0 formso0.
rewrite addr0; do 2 f_equal.
rewrite -(sumonb_out t2tv) tentf_sumr linear_sumr/= (bigD1 j2)//= big1=>[k /negPf nkj|];
by rewrite tentv_out ?addr0 outp_comp -!tentv_t2tv// 
  tentv_dot !t2tv_dot [_ == k]eq_sym nkj mulr0 scale0r.
Qed.

(* proposition 5.2 (1) : if statement law, truth-falsity *)
Lemma ifTK T (x : qreg T) c0 c1 :
  <{[ c0 ◁ M_T[x] ▷ c1 ]}> =c c1.
Proof.
rewrite eq_fsem.unlock fsemE/=; apply/eq_set=>y/=; 
  apply/propeqP; split=>[[x1 P1][x0 P0]<-|P1].
2: exists y=>//; move: (fsem_nonempty c0)=>[x0 P0]; exists x0=>//.
all: by rewrite tf2f1 liftf_lf1 formso1 comp_so1r !linear0 formso0 comp_so0r addr0.
Qed.

(* proposition 5.2 (3) : if statement law, complementation *)
Lemma if_compl T (x : qreg T) (M : 'QM(bool;'Ht T)) c0 c1 :
  <{[ c0 ◁ M ^m⟂[x] ▷ c1 ]}> =c <{[ c1 ◁ M[x] ▷ c0 ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE/=; apply/eq_set=>y/=; 
apply/propeqP; split=>[[x1 P1][x0 P0]<-|[x0 P0][x1 P1]<-].
by exists x0=>//; exists x1=>//; rewrite addrC.
by exists x1=>//; exists x0=>//; rewrite addrC.
Qed.

(* proposition 5.2 (1) : if statement law, truth-falsity *)
Lemma ifFK T (x : qreg T) c0 c1 :
  <{[ c0 ◁ M_F[x] ▷ c1 ]}> =c c0.
Proof.
rewrite -if_compl bcmeasF -{2}[c0](ifTK x c1).
by apply: eq_cond2=>i//=; rewrite bcmeasF.
Qed.

(* proposition 5.2 (2) : if statement law, idempotence *)
Lemma if_idem T (x : qreg T) M c {H : `{{no_nchoice_ c}}} :
  <{[ c ◁ M[x] ▷ c ]}> =c <{[ ('[ M[x] ]) ;; c ]}>.
Proof.
move: H=>/fsem_no_nchoice[x0 Pc].
rewrite eq_fsem.unlock !fsemE Pc !image2_set1; f_equal.
by rewrite !comp_so1l comp_soDr.
Qed.

(* proposition 5.2 (4) : if statement law, associativity *)
Lemma if_projKr T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 :
  let M := pmeas P in
  <{[ c0 ◁ M[x] ▷ (c1 ◁ M[x] ▷ c2) ]}> =c <{[ c0 ◁ M[x] ▷ c2 ]}>.
Proof.
rewrite /= eq_fsem.unlock !fsemE/=; apply/eq_set=>y/=; 
apply/propeqP; split=>[[?][x2 P2][x1 P1]<-[x0 P0]<-|[x2 P2][x0 P0]<-].
exists x2=>//; exists x0=>//.
2: move: (fsem_nonempty c1)=>[x1 P1];
  exists (x2 :o formso (liftf_lf (tf2f x x (pmeas P true))) +
    (x1 :o formso (liftf_lf (tf2f x x (pmeas P false)))));
  [exists x2=>//; exists x1=>//| exists x0=>//].
all: by rewrite linearDl/= -!comp_soA !formso_comp -!liftf_lf_comp
  !tf2f_comp projf_idem /pmeas hsE/= projf_cplmtMl !linear0 formso0 comp_so0r addr0.
Qed.

Lemma if_projKl T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 :
  let M := pmeas P in
  <{[ (c0 ◁ M[x] ▷ c1) ◁ M[x] ▷ c2 ]}> =c <{[ c0 ◁ M[x] ▷ c2 ]}>.
Proof.
rewrite /= -!(if_compl x (pmeas P)).
suff ->: bcmeas (pmeas P) = pmeas (~` P)%HS :> 'QM by apply: if_projKr.
by apply/qmeasureP=>//= i; rewrite /bcmeas /pmeas hsOK; case: i.
Qed.

Lemma if_projA T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 :
  let M := pmeas P in
  <{[ c0 ◁ M[x] ▷ (c1 ◁ M[x] ▷ c2) ]}> =c 
    <{[ (c0 ◁ M[x] ▷ c1) ◁ M[x] ▷ c2 ]}>.
Proof. by rewrite /= if_projKr if_projKl. Qed.

(* proposition 5.2 (5) : if statement law, if elimination *)
Lemma if_entail T (x : 'QReg[T]) (M N K : 'QM) c0 c1 :
  M ▶ N -> K ≅ M & N ->
    <{[ '( M[x] ] ;; (c0 ◁ N[x] ▷ c1) ]}> =c <{[ '( K[x] ] ;; c1 ]}>.
Proof.
move=>Q1 Q2; rewrite eq_fsem.unlock !fsemE/= !image2_set1; apply/eq_set=>y/=; 
apply/propeqP; split.
move=>[?][x1 P1][x0 P0]<-<-; exists x1=>//.
2: move: (fsem_nonempty c0)=>[x0 P0] [x1 P1]<-;
  exists (x1 :o formso (liftf_lf (tf2f x x (N true))) +
    (x0 :o formso (liftf_lf (tf2f x x (N false)))));
  first by exists x1=>//; exists x0=>//.
all: rewrite !comp_so1l !comp_so0l !addr0
  linearDl/= -!comp_soA !formso_comp -!liftf_lf_comp !tf2f_comp Q1;
  rewrite tf2f0 linear0 formso0 comp_so0r addr0; f_equal.
all: move: Q2=>[c Pc] /(f_equal (fun x=> c^-1 *: x));
  rewrite scalerA mulVf -1?normr_eq0 ?Pc ?oner_neq0// scale1r=><-;
  by rewrite !linearZ/= formso_eqZ// normfV Pc invr1.
Qed.

Lemma if_weaker T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ∝ N -> <{[ c1 ◁ N[x] ▷ (c2 ◁ M[x] ▷ c3) ]}> =c <{[ c1 ◁ N[x] ▷ c3 ]}>.
Proof.
move=>/meas_weakerP[] [c Pc P2] P1.
rewrite eq_fsem.unlock !fsemE.
apply/eq_set=>y; apply/propeqP; split=>/=.
- move=>[?][x3 Q3][x2 Q2]<-[x1 Q1]<-.
    exists x3=>//; exists x1=>//.
2: move: (fsem_nonempty c2)=>[x2 Q2][x3 Q3][x1 Q1]<-;
  exists (x3 :o formso (liftf_lf (tf2f x x (M true))) + 
    (x2 :o formso (liftf_lf (tf2f x x (M false)))));
    [by exists x3=>//; exists x2 | exists x1=>//].
all: rewrite comp_soDl -!comp_soA !formso_comp -!liftf_lf_comp 
  !tf2f_comp P1 tf2f0 linear0 formso0 comp_so0r addr0; do 2 f_equal.
all: by rewrite P2 !linearZ/= formso_eqZ.
Qed.

Lemma if_weakerrl T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ^m⟂ ∝ N -> <{[ c1 ◁ N[x] ▷ (c2 ◁ M[x] ▷ c3) ]}> =c <{[ c1 ◁ N[x] ▷ c2 ]}>.
Proof. by move=>P; rewrite -[X in cond2_ _ _ _ X]if_compl if_weaker. Qed.

Lemma if_weakerll T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ^m⟂ ∝ N ^m⟂ -> <{[ (c1 ◁ M[x] ▷ c2) ◁ N[x] ▷ c3 ]}> =c <{[ c1 ◁ N[x] ▷ c3 ]}>.
Proof. by move=>P; rewrite -if_compl if_weakerrl// if_compl. Qed.  

Lemma if_weakerlr T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ∝ N ^m⟂ -> <{[ (c1 ◁ M[x] ▷ c2) ◁ N[x] ▷ c3 ]}> =c <{[ c2 ◁ N[x] ▷ c3 ]}>.
Proof. by move=>P; rewrite -if_compl if_weaker// if_compl. Qed.  

(* Lemma 5.2 *)
Lemma meas_reducel T (x : 'QReg[T]) (N : 'QM) (M : 'QM) (K : 'QM) (L : 'QM) :
  <{[ '[ N[x] ) ]}> =c <{[ '[ K[x] ) ◁ M[x] ▷ '[ L[x] ) ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    ((K false \o M false) ⋈_(c0) (N false)) /\ ((L false \o M true) ⋈_(c1) (N false)).
Proof.
rewrite meas_proportionP; split.
  move=>+ r; rewrite eq_fsem.unlock !fsemE !image2_set1=>P.
  move: (eq_set1 P); rewrite !comp_so0l !comp_so1l !add0r.
  move/superopP=>/(_ (liftf_lf (tf2f x x r))).
  rewrite !soE -!liftf_lf_adj -!liftf_lf_comp !tf2f_adj !tf2f_comp -!linearD/=;
  by move=>/liftf_lf_inj/tf2f_inj->; rewrite addrC !adjf_comp !comp_lfunA.
move=>P; rewrite eq_fsem.unlock !fsemE !image2_set1; f_equal.
rewrite !comp_so0l !comp_so1l !add0r.
rewrite -!liftfso_formso -!liftfso_comp -linearD/=; f_equal.
apply/superopP=>r; rewrite -(f2tfK r); set r' := f2tf r.
by rewrite !soE !tf2f_adj !tf2f_comp -linearD/= -P addrC !adjf_comp !comp_lfunA.
Qed.

Lemma meas_reducer T (x : 'QReg[T]) (N : 'QM) (M : 'QM) (K : 'QM) (L : 'QM) :
  <{[ '( N[x] ] ]}> =c <{[ '( K[x] ] ◁ M[x] ▷ '( L[x] ] ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    ((K true \o M false) ⋈_(c0) (N true)) /\ ((L true \o M true) ⋈_(c1) (N true)).
Proof. by rewrite -![ cond2_ _ _ abort_ _]if_compl meas_reducel/= !/bcmeas/=. Qed.

Lemma meas_aborbl T (x : 'QReg[T]) (N : 'QM) (M : 'QM) :
  <{[ '[ N[x] ) ]}> =c <{[ '[ M[x] ] ;; '[ N[x] ) ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    (N false ⋊_(c0) M false) /\ (N false ⋊_(c1) M true).
Proof.
rewrite meas_aborb; split.
  move=>+ r; rewrite eq_fsem.unlock !fsemE !image2_set1=>P.
  move: (eq_set1 P); rewrite !comp_so0l !comp_so1l !add0r.
  move/superopP=>/(_ (liftf_lf (tf2f x x r))).
  rewrite !soE -!liftf_lf_adj !tf2f_adj -!liftf_lf_comp 
    !tf2f_comp -!linearD/= -!liftf_lf_comp !tf2f_comp.
  by move=>/liftf_lf_inj/tf2f_inj->; rewrite addrC !linearDr/= linearDl/= !comp_lfunA.
move=>P; rewrite eq_fsem.unlock !fsemE !image2_set1; f_equal.
rewrite !comp_so0l !comp_so1l !add0r.
rewrite -!liftfso_formso -linearD -!liftfso_comp; f_equal.
apply/superopP=>r; rewrite -(f2tfK r); set r' := f2tf r.
by rewrite !soE !tf2f_adj !tf2f_comp -linearD/= 
  !tf2f_comp linearDr/= linearDl/= -P addrC !comp_lfunA.
Qed.

Lemma meas_aborbr T (x : 'QReg[T]) (N : 'QM) (M : 'QM) :
  <{[ '( N[x] ] ]}> =c <{[ '[ M[x] ] ;; '( N[x] ] ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    (N true ⋊_(c0) M false) /\ (N true ⋊_(c1) M true).
Proof. by rewrite -![ cond2_ _ _ abort_ _]if_compl meas_aborbl/= !/bcmeas/=. Qed.

(* proposition 5.3 (1) : nested if statement law, reduction *)
(* for nondeterministic program, we further need to assume that c0 *)
(* and c1 are deterministic, i.e., without nchoice                 *)
Lemma if_reduce T1 T2 T3 T4 (x1 : qreg T1) (x2 : qreg T2) (x3 : qreg T3)
  (x4 : qreg T4) (N : 'QM) (M : 'QM) (K : 'QM) (L : 'QM) c0 c1 
  {Hc0 : `{{no_nchoice_ c0}}} {Hc1 : `{{no_nchoice_ c1}}} :
  <{[ '( N[x1] ] ]}> =c <{[ '( K[x3] ] ◁ M[x2] ▷ '( L[x4] ] ]}> ->
  <{[ '[ N[x1] ) ]}> =c <{[ '[ K[x3] ) ◁ M[x2] ▷ '[ L[x4] ) ]}> ->
  <{[ (c0 ◁ K[x3] ▷ c1) ◁ M[x2] ▷ (c0 ◁ L[x4] ▷ c1) ]}> =c <{[ c0 ◁ N[x1] ▷ c1 ]}>.
Proof.
move: Hc0 Hc1=>/fsem_no_nchoice [y0 P0] /fsem_no_nchoice [y1 P1].
rewrite eq_fsem.unlock !fsemE !P0 !P1 !image2_set1 !comp_so0l !comp_so1l !add0r !addr0.
move=>H1 H2; move: (eq_set1 H1) (eq_set1 H2)=>->->; f_equal.
by rewrite !linearDl/= addrACA -!comp_soA -!linearDr/=.
Qed.

Lemma if_reduce_tmeas T1 T2 (x1 : qreg T1) (x2 : qreg T2) 
  (P : evalQT T1 -> evalQT T2 -> cmd_) {H : `{{disjoint_qreg x1 x2}}} :
  <{[ If tmeas[x1] = m then <{[ If tmeas[x2] = n then P m n fI ]}> fI  ]}> 
  =c <{[ If tmeas[(x1,x2)] = k then P k.1 k.2 fI ]}>.
Proof.
move: H; rewrite /cmd_expose=>H.
rewrite eq_fsem.unlock !fsemE; apply/eq_set=>?/=; apply/propeqP; split.
- move=>[f1[] <-] P2.
  have P3 i : exists l : evalQT T2 -> 'SO_setT, 
    ifso (liftf_fun (tm2m x2 x2 tmeas)) l = f1 i /\ forall j, fsem (P i j) (l j).
    by move: (P2 i); rewrite fsemE/=.
  exists (fun k => projT1 (cid (P3 k.1)) k.2).
  split; last first.
    by move=>[i j]/=; move: (projT2 (cid (P3 i)))=>[] _ /(_ j).
  rewrite !ifso_elem pair_bigV/=; apply eq_bigr=>i _.
  move: (projT2 (cid (P3 i)))=>[] {6}<- Pj.
  rewrite ifso_elem linear_suml/=; apply eq_bigr=>j _.
  rewrite -comp_soA; f_equal.
  rewrite /elemso !liftf_funE !tm2mE formso_comp !tmeasE -tentv_t2tv 
    -tentv_out -tf2f_pair liftf_lf_cast liftf_lf_compC ?liftf_lf_compT//.
  by rewrite disjoint_sym -disj_setE. by rewrite -disj_setE.
move=>[l [ <- Pi]].
exists (fun i => ifso (liftf_fun (tm2m x2 x2 tmeas)) (fun j => l (i,j))).
split; last first.
  move=>i; rewrite fsemE/=; exists (fun j => l (i,j)); split=>//.
  by move=>j; move: (Pi (i,j)).
rewrite !ifso_elem.
under eq_bigr do rewrite ifso_elem linear_suml/=.
rewrite pair_big/=; apply eq_bigr=>[[m n]] _ /=.
rewrite -comp_soA; f_equal.
rewrite /elemso !liftf_funE !tm2mE formso_comp !tmeasE -tentv_t2tv 
  -tentv_out -tf2f_pair liftf_lf_cast liftf_lf_compC ?liftf_lf_compT//.
by rewrite disjoint_sym -disj_setE. by rewrite -disj_setE.
Qed.

(* proposition 5.3 (2) : nested if statement law, left-distributivity *)
(* for nondeterministic program, we further need to assume that c0 *)
(* is deterministic, i.e., without nchoice                         *)
Lemma if_distrr T (x : 'QReg[T]) (N M : 'QM) c0 c1 c2 {Hc0 : `{{no_nchoice_ c0}}} :
  M ◇L N -> <{[ '[ N[x] ) ]}> =c <{[ '[ M[x] ] ;; '[ N[x] ) ]}> ->
    <{[ c0 ◁ N[x] ▷ (c1 ◁ M[x] ▷ c2) ]}> =c 
      <{[ (c0 ◁ N[x] ▷ c1) ◁ M[x] ▷ (c0 ◁ N[x] ▷ c2) ]}>.
Proof.
move: Hc0=>/fsem_no_nchoice[x0 P0] []H1 H2.
rewrite eq_fsem.unlock !fsemE P0 !image2_set1 !comp_so1l !comp_so0l !add0r=>H3.
move: (eq_set1 H3)=>{1}->; apply/eq_set=>y/=; apply/propeqP; split.
  move=>[?][x2 P2][x1 P1]<-<-.
  exists (x2 :o formso (liftf_lf (tf2f x x (N true))) + 
    (x0 :o formso (liftf_lf (tf2f x x (N false))))); first by exists x2.
  exists (x1 :o formso (liftf_lf (tf2f x x (N true))) + 
    (x0 :o formso (liftf_lf (tf2f x x (N false))))); first by exists x1.
  rewrite !linearDl/= addrACA -linearDr/= -!comp_soA; do 3 f_equal;
  by rewrite !formso_comp -!liftf_lf_comp !tf2f_comp ?H1 ?H2.
move=>[?][x2 P2]<-[?][x1 P1]<-<-.
exists (x2 :o formso (liftf_lf (tf2f x x (M true))) + 
  (x1 :o formso (liftf_lf (tf2f x x (M false))))); first by exists x2=>//; exists x1.
rewrite !linearDl/= addrACA -linearDr/= -!comp_soA; do 3 f_equal;
by rewrite !formso_comp -!liftf_lf_comp !tf2f_comp ?H1 ?H2.
Qed.

(* proposition 5.3 (3) : nested if statement law, right-distributivity *)
(* for nondeterministic program, we further need to assume that c2 *)
(* is deterministic, i.e., without nchoice                         *)
Lemma if_distrl T (x : 'QReg[T]) (N M : 'QM) c0 c1 c2 {Hc2 : `{{no_nchoice_ c2}}} :
  M ◇R N -> <{[ '( N[x] ] ]}> =c <{[ ('[ M[x] ]) ;; ('( N[x] ]) ]}> ->
  <{[ (c0 ◁ M[x] ▷ c1) ◁ N[x] ▷ c2 ]}> =c 
    <{[ (c0 ◁ N[x] ▷ c2) ◁ M[x] ▷ (c1 ◁ N[x] ▷ c2) ]}>.
Proof.
move: Hc2 => /fsem_no_nchoice[x2 P2] []H1 H2.
rewrite eq_fsem.unlock !fsemE P2 !image2_set1 !comp_so1l !comp_so0l !addr0=>H3.
move: (eq_set1 H3)=>{1}->; apply/eq_set=>y/=; apply/propeqP; split.
  move=>[?][x1 P1][x0 P0]<-<-.
  exists (x2 :o formso (liftf_lf (tf2f x x (N true))) + 
    (x1 :o formso (liftf_lf (tf2f x x (N false))))); first by exists x1.
  exists (x2 :o formso (liftf_lf (tf2f x x (N true))) + 
    (x0 :o formso (liftf_lf (tf2f x x (N false))))); first by exists x0.
  rewrite !linearDl/= addrACA -linearDr/= -!comp_soA; do 3 f_equal;
  by rewrite !formso_comp -!liftf_lf_comp !tf2f_comp ?H1 ?H2.
move=>[?][x1 P1]<-[?][x0 P0]<-<-.
exists (x1 :o formso (liftf_lf (tf2f x x (M true))) + 
  (x0 :o formso (liftf_lf (tf2f x x (M false))))); first by exists x1=>//; exists x0.
rewrite !linearDl/= addrACA -linearDr/= -!comp_soA; do 3 f_equal;
by rewrite !formso_comp -!liftf_lf_comp !tf2f_comp ?H1 ?H2.
Qed.

(* proposition 5.3 (4) : nested if statement law, left-distributivity for projection *)
Lemma if_proj_distrr T (x : 'QReg[T]) (X Y : {hspace 'Ht T}) c0 c1 c2 {Hc0 : `{{no_nchoice_ c0}}} :
  pmeas X ▶ pmeas Y \/ pmeas (~` X)%HS ▶ pmeas Y ->
    <{[ c0 ◁ pmeas Y[x] ▷ (c1 ◁ pmeas X [x] ▷ c2) ]}> =c 
      <{[ (c0 ◁ pmeas Y[x] ▷ c1) ◁ pmeas X[x] ▷ (c0 ◁ pmeas Y[x] ▷ c2) ]}>.
Proof.
move=>P; apply: if_distrr.
by case: P=>/pmeas_entail_lcom //; rewrite -pmeas_lcomOx.
rewrite eq_fsem.unlock !fsemE !image2_set1; f_equal.
rewrite comp_so0l !comp_so1l add0r -!liftfso_formso -linearD/= -liftfso_comp.
f_equal; apply/superopP=>r; rewrite !soE linearDr linearDl/= !tf2f_adj !comp_lfunA !tf2f_comp.
case: P; rewrite pmeas_entailP; first rewrite -lehO.
all: move=>P1; move: P1 {+}P1.
rewrite {1}leh_compl0 leh_compl hsOK /pmeas=>/eqP->/eqP P1.
by rewrite linear0 !linear0l add0r P1 -!comp_lfunA tf2f_comp -adjf_comp P1.
rewrite {1}leh_compr0 lehOx leh_compl /pmeas=>/eqP->/eqP P1.
by rewrite linear0 !linear0l addr0 P1 -!comp_lfunA tf2f_comp -adjf_comp P1.
Qed.

(* proposition 5.3 (5) : nested if statement law, right-distributivity for projection *)
Lemma if_proj_distrl T (x : 'QReg[T]) (X Y : {hspace 'Ht T}) c0 c1 c2 {Hc2 : `{{no_nchoice_ c2}}} :
  pmeas Y ▶ pmeas X \/ pmeas Y ▶ pmeas (~` X)%HS ->
    <{[ (c0 ◁ pmeas X[x] ▷ c1) ◁ pmeas Y[x] ▷ c2 ]}> =c 
      <{[ (c0 ◁ pmeas Y[x] ▷ c2) ◁ pmeas X[x] ▷ (c1 ◁ pmeas Y[x] ▷ c2) ]}>.
Proof.
move=>P1; rewrite -![ cond2_ _ (pmeas _) _ _]if_compl !pmeasO_qmE; apply/if_proj_distrr.
by rewrite -2!pmeas_entailO.
Qed.

(* proposition 5.4 (1) : sequential composition, unit and zero *)
Lemma skipIx c : <{[ skip ;; c ]}> =c c.
Proof.
rewrite eq_fsem.unlock !fsemE image2_set1; apply/eq_set=>x;
by apply/propeqP; split; [move=>[?+<-]|exists x=>//]; rewrite comp_so1r.
Qed.

Lemma skipxI c : <{[ c ;; skip ]}> =c c.
Proof.
rewrite eq_fsem.unlock !fsemE image2_set1; apply/eq_set=>x;
by apply/propeqP; split; [move=>[?+<-]|exists x=>//]; rewrite comp_so1l.
Qed.

Lemma skipC c : <{[ skip ;; c ]}> =c <{[ c ;; skip ]}>.
Proof. by rewrite skipIx skipxI. Qed.

Lemma abortIx c : <{[ abort ;; c ]}> =c <{[ abort ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE image2_set1; apply/eq_set=>x.
apply/propeqP; split; first by move=>[? + <-]; rewrite comp_so0r.
by move=>->; move: (fsem_nonempty c)=>[x0 P0]; exists x0=>//; rewrite comp_so0r.
Qed.

Lemma abortxI c : <{[ c ;; abort ]}> =c <{[ abort ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE image2_set1; apply/eq_set=>x.
apply/propeqP; split; first by move=>[? + <-]; rewrite comp_so0l.
by move=>->; move: (fsem_nonempty c)=>[x0 P0]; exists x0=>//; rewrite comp_so0l.
Qed.

Lemma abortC c : <{[ abort ;; c ]}> =c <{[ c ;; abort ]}>.
Proof. by rewrite abortIx abortxI. Qed.

(* proposition 5.4 (2) : sequential composition, commutativity *)
Lemma seqcC c1 c2 {H : `{{cmd_disj c1 c2}}} :
  <{[ c1 ;; c2 ]}> =c <{[ c2 ;; c1 ]}>.
Proof.
move: H=>/cmd_disjP P0; rewrite eq_fsem.unlock !fsemE.
apply/eq_set=>x; apply/propeqP; split.
move=>[x1 P1][x2 P2]<-; exists x2=>//; exists x1=>//.
2: move=>[x2 P2][x1 P1]<-; exists x1=>//; exists x2=>//.
all: move: (fsem_local P1) (fsem_local P2)=>[U1 ->][U2 ->];
  by rewrite liftfso_compC // disjoint_sym.
Qed.

(* proposition 5.4 (3) : sequential composition, associativity *)
Lemma seqcA c0 c1 c2 :
  <{[ c0 ;; c1 ;; c2 ]}> =c <{[ c0 ;; (c1 ;; c2) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE;
apply/eq_set=>x; apply/propeqP; split.
by move=>/=[?][x0 P0][x1 P1]<-[x2 P2]<-; exists x0=>//; exists (x2 :o x1)=>//; 
  [exists x1=>//; exists x2=>//|rewrite comp_soA].
by move=>[x0 P0][?][x1 P1][x2 P2]<-<-; exists (x1 :o x0);
  [exists x0=>//; exists x1|exists x2] =>//; rewrite comp_soA.
Qed.

Lemma seqc_circuitA c u1 u2 : 
  <{[ c ;; [cir u1 ; u2 ] ]}> =c <{[ c ;; ([cir u1 ]) ;; [cir u2 ] ]}>.
Proof. by rewrite seqc_circuit seqcA. Qed.

(* proposition 5.4 (4) : sequentiality *)
Lemma if_seqc T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 c3 
  {H0 : `{{ cmd_var_disj x c0 }}} {H1 : `{{ cmd_var_disj x c1 }}} :
  let M := pmeas P in
  <{[ (c0 ◁ M[x] ▷ c1) ;; (c2 ◁ M[x] ▷ c3) ]}> =c 
    <{[ (c0 ;; c2) ◁ M[x] ▷ (c1 ;; c3) ]}>.
Proof.
move=>M.
rewrite eq_fsem.unlock !fsemE; apply/eq_set=>?/=; apply/propeqP; split.
  move=>[?] [x1 Q1] [x0 Q0] <- [?] [x3 Q3] [x2 Q2] <- <-.
  exists (x3 :o x1); first by exists x1=>//; exists x3.
  exists (x2 :o x0); first by exists x0=>//; exists x2.
  move: (fsem_local Q0) (fsem_local Q1) => [e0 P0] [e1 P1].
  rewrite P0 P1 -!liftfso_formso -!comp_soA.
  rewrite ![liftfso _ :o liftfso (formso _)]liftfso_compC.
  1,2: by rewrite disjoint_sym; apply/cmd_var_disjP.
  rewrite comp_soDl !comp_soDr !comp_soA !comp_soACA -!liftfso_comp !formso_comp
    !tf2f_comp.
  by rewrite /= /pmeas hsOx_comp hsxO_comp tf2f0 formso0 linear0 
    !(comp_so0r, comp_so0l) addr0 add0r !projf_idem.
move=>[?] [x1 Q1] [x3 Q3] <- [?] [x0 Q0] [x2 Q2] <-<-.
exists (x1 :o formso (liftf_lf (tf2f x x (pmeas P true))) +
      (x0 :o formso (liftf_lf (tf2f x x (pmeas P false))))).
  by exists x1=>//; exists x0.
exists (x3 :o formso (liftf_lf (tf2f x x (pmeas P true))) +
      (x2 :o formso (liftf_lf (tf2f x x (pmeas P false))))).
  by exists x3=>//; exists x2.
move: (fsem_local Q0) (fsem_local Q1) => [e0 P0] [e1 P1].
rewrite P0 P1 -!liftfso_formso -!comp_soA.
rewrite ![liftfso _ :o liftfso (formso _)]liftfso_compC.
1,2: by rewrite disjoint_sym; apply/cmd_var_disjP.
rewrite comp_soDl !comp_soDr !comp_soA !comp_soACA -!liftfso_comp !formso_comp
  !tf2f_comp.
by rewrite /= /pmeas hsOx_comp hsxO_comp tf2f0 formso0 linear0 
  !(comp_so0r, comp_so0l) addr0 add0r !projf_idem.
Qed.

(* proposition 5.4 (5) : sequential composition, right-distributivity *)
(* for nondeterministic program, we further need to assume that c  *)
(* is deterministic, i.e., without nchoice                         *)
Lemma seqc_distrl T (x : qreg T) M c0 c1 c {Hc : `{{no_nchoice_ c}}} :
  <{[ (c0 ◁ M[x] ▷ c1) ;; c ]}> =c <{[ (c0 ;; c) ◁ M[x] ▷ (c1 ;; c) ]}>.
Proof.
move: Hc=>/fsem_no_nchoice[x2 P2]; rewrite eq_fsem.unlock !fsemE P2 !image2_set1.
apply/eq_set=>y; apply/propeqP; split=>/=.
  move=>[?][x1 P1][x0 P0]<-<-.
  exists (x2 :o x1); first by exists x1.
  exists (x2 :o x0); first by exists x0.
  by rewrite comp_soDr !comp_soA.
move=>[?][x1 P1]<-[?][x0 P0]<-<-.
exists (x1 :o formso (liftf_lf (tf2f x x (M true))) + (x0 :o formso (liftf_lf (tf2f x x (M false))))).
by exists x1=>//; exists x0.
by rewrite comp_soDr !comp_soA.
Qed.

(* proposition 5.4 (6) : sequential composition, left-distributivity-I *)
(* for nondeterministic program, we further need to assume that c  *)
(* is deterministic, i.e., without nchoice                         *)
Lemma seqc_distrr T (x : qreg T) M c0 c1 c 
  {H : `{{cmd_var_disj x c}}} {Hc : `{{no_nchoice_ c}}} :
  <{[ c ;; (c0 ◁ M[x] ▷ c1) ]}> =c <{[ (c ;; c0) ◁ M[x] ▷ (c ;; c1) ]}>.
Proof.
move: Hc=>/fsem_no_nchoice[x2 P2]; rewrite eq_fsem.unlock !fsemE P2 !image2_set1.
apply/eq_set=>y; apply/propeqP; split=>/=.
  move=>[?][x1 P1][x0 P0]<-<-.
  exists (x1 :o x2); first by exists x1.
  exists (x0 :o x2); first by exists x0.
  have /fsem_local [e ->] : fsem c x2 by rewrite P2.
  by rewrite comp_soDl -!comp_soA -!liftfso_formso
    ![_ :o liftfso e]liftfso_compC// cmd_var_disjP.
move=>[?][x1 P1]<-[?][x0 P0]<-<-.
exists (x1 :o formso (liftf_lf (tf2f x x (M true))) + 
  (x0 :o formso (liftf_lf (tf2f x x (M false))))).
by exists x1=>//; exists x0.
have /fsem_local [e ->] : fsem c x2 by rewrite P2.
by rewrite comp_soDl -!comp_soA -!liftfso_formso
  ![_ :o liftfso e]liftfso_compC// cmd_var_disjP.
Qed.

(* proposition 5.4 (7) : sequential composition, left-distributivity *)
(* for nondeterministic program, we further need to assume that c  *)
(* is deterministic, i.e., without nchoice                         *)
Lemma seqc_distrr2 T1 T2 (x1 : qreg T1) (x2 : qreg T2) (M : 'QM) (N : 'QM) 
  c c0 c1 {Hc : `{{no_nchoice_ c}}} :
  <{[ c ;; ('[ M[x1] )) ]}> =c <{[ ('[ N[x2] )) ;; c ]}> ->
  <{[ c ;; ('( M[x1] ]) ]}> =c <{[ ('( N[x2] ]) ;; c ]}> ->
  <{[ c ;; (c0 ◁ M[x1] ▷ c1) ]}> =c <{[ (c ;; c0) ◁ N[x2] ▷ (c ;; c1) ]}>.
Proof.
move: Hc=>/fsem_no_nchoice[x P].
rewrite eq_fsem.unlock !fsemE !P !image2_set1 !comp_so0l !add0r !addr0 !comp_so1l=>H1 H2.
apply/eq_set=>y; apply/propeqP; split=>/=.
  move=>[?][y1 P1][y0 P0]<-<-.
  exists (y1 :o x); first by exists y1.
  exists (y0 :o x); first by exists y0.
  by rewrite comp_soDl -!comp_soA; do 2 f_equal; apply/eq_set1.
move=>[?][y1 P1]<-[?][y0 P0]<-<-.
exists (y1 :o formso (liftf_lf (tf2f x1 x1 (M true))) + 
  (y0 :o formso (liftf_lf (tf2f x1 x1 (M false))))); first by exists y1=>//; exists y0.
by rewrite comp_soDl -!comp_soA; do 2 f_equal; apply/eq_set1.
Qed.

Lemma seqc_distrUr T (x : 'QReg[T]) (M : 'QM) (U : 'FU) c0 c1 :
  let UM := measUr M U in
  <{[ ([cir [x] *= U ]) ;; (c0 ◁ M[x] ▷ c1) ]}> =c 
    <{[ c0 ◁ UM[x] ▷ c1 ]}>.
Proof.
rewrite /= eq_fsem.unlock !fsemE !image2_set1 usemE.
apply/eq_set=>y; apply/propeqP; split=>/=.
move=>[?][x1 P1][x0 P0]<-<-; exists x1=>//; exists x0=>//.
2: move=>[x1 P1][x0 P0]<-;
  exists (x1 :o formso (liftf_lf (tf2f x x (M true))) + 
  (x0 :o formso (liftf_lf (tf2f x x (M false))))); first by exists x1=>//; exists x0.
all: rewrite comp_soDl -!comp_soA; do 2 f_equal;
by rewrite formso_comp -liftf_lf_comp tf2f_comp.
Qed.

(* Proposition 5.5 : qif - if interplay *)
Lemma qif_if T (F : finType) (x : 'QReg[T]) (phi : 'ONB(F; 'Ht T)) 
  (u : F -> ucmd_) (c : F -> cmd_) {H : `{{forall i, (ucmd_var_disj x (u i))}}}:
  <{[ [cir qif phi[x] = i then u i fiq] ;; If (onb_meas phi)[x] = i then c i fI]}> =c <{[ If (onb_meas phi)[x] = i then seqc_ (circuit_ (u i)) (c i) fI]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !image2_set1.
apply/eq_set=>y; apply/propeqP; split=>/=.
- move=>[?] [l [ <- Pl] <-].
  exists (fun i => l i :o formso (usem (u i))); split; last first.
    move=>i; rewrite fsemE/=.
    exists (formso (usem (u i))); first by rewrite fsemE.
    by exists (l i).
  rewrite usemE !ifso_elem linear_suml/=.
  apply eq_bigr=>i _; rewrite /elemso liftf_funE tm2mE onb_measE 
    -!comp_soA !formso_comp; do 2 f_equal.
  rewrite linear_sumr/= (bigD1 i)//= big1=>[j /negPf nji|];
  rewrite !comp_lfunA -liftf_lf_comp tf2f_comp outp_comp onb_dot.
  by rewrite eq_sym nji scale0r !linear0 !comp_lfun0l.
  move: (usem_local (u i))=>[U ->].
  rewrite eqxx scale1r addr0 [in RHS]liftf_lf_compC ?ucmd_var_disj_vsetP//.
  by rewrite -comp_lfunA -liftf_lf_comp tf2f_comp outp_comp ns_dot scale1r.
move=>[l] [ <- Pl].
have Pi (i : F) :  exists y, fsem (c i) y /\ y :o (formso (usem (u i))) = l i.
  move: (Pl i); rewrite fsemE/==>[[? +][z Pz <-]].
  by rewrite fsemE/==>->; exists z.
exists (ifso (liftf_fun (tm2m x x (onb_meas phi))) (fun i => projT1 (cid (Pi i)))).
exists (fun i : F => projT1 (cid (Pi i))); split=>// i.
  by move: (projT2 (cid (Pi i)))=>[].
rewrite usemE !ifso_elem linear_suml/=.
apply eq_bigr=>i _; rewrite /elemso liftf_funE tm2mE onb_measE 
  -!comp_soA !formso_comp.
move: (projT2 (cid (Pi i)))=>[] _ {3}<-.
rewrite linear_sumr/= (bigD1 i)//= big1=>[j /negPf nji|];
rewrite !comp_lfunA -liftf_lf_comp tf2f_comp outp_comp onb_dot.
by rewrite eq_sym nji scale0r !linear0 !comp_lfun0l.
move: (usem_local (u i))=>[U Pu].
rewrite eqxx scale1r addr0 {3}Pu [in LHS]liftf_lf_compC ?ucmd_var_disj_vsetP//.
rewrite -comp_lfunA -liftf_lf_comp tf2f_comp outp_comp ns_dot scale1r.
by rewrite -formso_comp -Pu comp_soA.
Qed.

Lemma whilegso_fixpointP (U : chsType) (M : 'TN(bool;U)) (f : nat -> 'SO(U)) :
  (forall i, f i \is cptn) ->
  (whilegso M (fun i : nat => f i.+1) :o f 0%N) :o formso (M true) + formso (M false) =
  whilegso M f.
Proof.
move=>Pf; pose g i := QOperation_Build (Pf i).
have ->: f = g by apply/funext=>i.
apply: whilegso_fixpoint.
Qed.

(* proposition 6.3 (1) : loop law, fixpoint  *)
Lemma while_fixpoint T (x : 'QReg[T]) M P :
  <{[ M[x] * P ]}> =c <{[ M[x] ▷ (P ;; (M[x] * P)) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !image2_set1 comp_so1l.
apply/eq_set=>y; apply/propeqP; split=>/=.
  move=>[]l[]<- Pl.
  exists (whilegso (liftf_fun (tm2m x x M)) (fun i=> l i.+1) :o (l 0%N)).
    exists (l 0%N)=>//; exists (whilegso (liftf_fun (tm2m x x M)) (fun i=> l i.+1))=>//.
    by exists (fun i=> l i.+1).
  by apply: whilegso_fixpointP; move=>i; apply: (fsem_qo (Pl i)).
move=>[?][x0 P0][?][l][]<- Pl<-<-.
exists (fun i=> match i with 0 => x0 | S n => l n end); split; last by case.
by rewrite -whilegso_fixpointP//=; case=>[|n]; apply: (@fsem_qo P).
Qed.

(* proposition 6.3 (2) : loop law, unfolding *)
Lemma while_unfold T (x : 'QReg[T]) (M N : 'QM) P :
  M ∝ N -> <{[ N[x] ▷ (M[x] * P) ]}> =c <{[ N[x] ▷ (P ;; (M[x] * P)) ]}>.
Proof. by rewrite {1}while_fixpoint; apply: if_weaker. Qed.

(* proposition 6.3 (2) : loop law, elimination *)
Lemma while_elim T (x : 'QReg[T]) (M N : 'QM) P :
  M ^m⟂ ∝ N -> <{[ N[x] ▷ (M[x] * P) ]}> =c <{[ '[ N[x] ] ]}>.
Proof. by rewrite while_fixpoint; apply: if_weakerrl. Qed.

(* proposition 6.3 (3) : loop law, postcondition *)
Lemma while_post T (x : 'QReg[T]) (M N : 'QM) P :
  N ≫ M -> <{[ M[x] * P ]}> =c <{[ (M[x] * P) ;; ('[ N[x] ]) ]}>.
Proof.
move=>/meas_contradictP [] [c Pc P1] P2.
rewrite eq_fsem.unlock !fsemE !image2_set1 !comp_so1l.
apply/eq_set=>y; apply/propeqP; split=>/=.
move=>[l][]<-Pl; exists (whilegso (liftf_fun (tm2m x x M)) l); first by exists l.
2: move=>[?][]l[]<- Pl<-; exists l; split=>//; symmetry.
all: rewrite whilegso.unlock -so_comp_limr; first apply: whilegso_is_cvgn.
1,4: by move: (@is_trnincr _ _ _ (liftf_fun (tm2m x x M))); 
  rewrite /trace_nincr big_bool/= addrC.
1,3: by move=>i; apply: (fsem_qo (Pl i)).
all: apply: eq_lim=>i; rewrite -linear_sumr/= comp_soA; f_equal;
  by rewrite linearDl/= !formso_comp liftf_funE -!liftf_lf_comp tm2mE 
    !tf2f_comp P2 tf2f0 linear0 formso0 addr0 P1 !linearZ/=; apply: formso_eqZ.
Qed.

(* proposition 7.1 (1) : nondeterministic law, commutativity *)
Lemma nchoiceC c1 c2 : <{[ c1 ⊔ c2 ]}> =c <{[ c2 ⊔ c1 ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE setUC. Qed.

(* proposition 7.1 (2) : nondeterministic law, associativity *)
Lemma nchoiceA c1 c2 c3 : 
  <{[ c1 ⊔ (c2 ⊔ c3) ]}> =c <{[ c1 ⊔ c2 ⊔ c3 ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE setUA. Qed.

(* proposition 7.1 (3) : nondeterministic law, idempotence *)
Lemma nchoicexx c : <{[ c ⊔ c ]}> =c c.
Proof. by rewrite eq_fsem.unlock !fsemE setUid. Qed.

(* proposition 7.1 (4) : nondeterministic law, distributivity over if *)
Lemma nchoice_if_distrr T (x : qreg T) M c0 c1 c2 :
  <{[ c0 ⊔ c1 ◁ M[x] ▷ c2 ]}> =c <{[ (c0 ◁ M[x] ▷ c2) ⊔ (c1 ◁ M[x] ▷ c2) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE.
apply/eq_set=>y; apply/propeqP; split=>/=.
  by move=>[x2 P2][x01][|]P01<-;[left|right]; exists x2=>//; exists x01.
by move=>[][x2 P2][x01 P01]<-; exists x2=>//; exists x01=>//; [left|right].
Qed.

Lemma nchoice_if_distrl T (x : qreg T) M c0 c1 c2 :
  <{[ c0 ◁ M[x] ▷ c1 ⊔ c2 ]}> =c <{[ (c0 ◁ M[x] ▷ c1) ⊔ (c0 ◁ M[x] ▷ c2) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE.
apply/eq_set=>y; apply/propeqP; split=>/=.
  by move=>[x12][|]P01[x0 P0]<-;[left|right]; exists x12=>//; exists x0.
by move=>[][x12 P12][x0 P0]<-; exists x12; auto; exists x0.
Qed.

(* proposition 7.1 (5) : nondeterministic law, distributivity over seqc *)
Lemma nchoice_seqc_distrr c0 c1 c2 :
  <{[ c0 ;; (c1 ⊔ c2) ]}> =c <{[ (c0 ;; c1) ⊔ (c0 ;; c2) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE.
apply/eq_set=>y; apply/propeqP; split=>/=.
  by move=>[x0 P0][x12][]P12<-; [left|right]; exists x0=>//; exists x12.
by move=>[][x0 P0][x12 P12]<-; exists x0=>//; exists x12=>//; [left|right].
Qed.

Lemma nchoice_seqc_distrl c0 c1 c2 :
  <{[ c0 ⊔ c1 ;; c2 ]}> =c <{[ (c0 ;; c2) ⊔ (c1 ;; c2) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE.
apply/eq_set=>y; apply/propeqP; split=>/=.
  by move=>[x01][]P01[x2 P2]<-; [left|right]; exists x01=>//; exists x2.
by move=>[][x01 P01][x2 P2]<-; exists x01; auto; exists x2.
Qed.

End NonDeterministicLaws.

Section ConvFsem.

Lemma fsem_seqcE2 c1 c2 :
  fsem <{[ c1 ;; c2 ]}> = fsem c2 `:o` fsem c1.
Proof.
rewrite fsemE /set_compso; apply/seteqP; split=>x /=;
by move=>[x1 P1][x2 P2]<-; exists x2=>//; exists x1.
Qed.

Lemma fsem_condE2 T (F : finType) (x : qreg T) (M : 'QM(F;'Ht T)) (f : F -> cmd_) :
  fsem (cond_ x M f) = \sum_(i : F) 
    (fsem (f i) `:o` [set formso (liftf_lf (tf2f x x (M i)))]).
Proof.
rewrite fsemE; apply/seteqP; split=>y /=.
  move=>[l][]<- Pi; rewrite -inE; apply/big_set_addP.
  exists (fun i => l i :o formso (liftf_lf (tf2f x x (M i)))); split.
  by move=>i; rewrite inE /set_compso; rewrite image2_set1/=; exists (l i).
  by rewrite ifso_elem; apply eq_bigr=>i _; rewrite /elemso liftf_funE tm2mE.
rewrite -inE=>/big_set_addP[g [Pg <-]].
have Pgi i : exists2 l, fsem (f i) l & (l :o formso (liftf_lf (tf2f x x (M i))) = g i).
  by move: (Pg i); rewrite inE /set_compso image2_set1/=.
exists (fun i => projT1 (cid2 (Pgi i))); split.
rewrite ifso_elem; apply eq_bigr=>i _.
by move: (projT2 (cid2 (Pgi i)))=>[] _; rewrite /elemso liftf_funE tm2mE.
by move=>i; move: (projT2 (cid2 (Pgi i)))=>[].
Qed.

Lemma fsem_cond2E2 T (x : qreg T) (M : 'QM(bool;'Ht T)) c0 c1 :
  fsem (cond2_ x M c0 c1) = 
      (fsem c0 `:o` [set formso (liftf_lf (tf2f x x (M false)))])
      + (fsem c1 `:o` [set formso (liftf_lf (tf2f x x (M true)))]).
Proof. by rewrite cond2_.unlock fsem_condE2 big_bool/= addrC. Qed.

Lemma fsem_pchoiceE2 p c1 c2 :
  fsem (pchoice_ p c1 c2) = 
    (val p) `*:` fsem c1 + (1 - val p) `*:` fsem c2.
Proof.
rewrite fsemE /set_scale; apply/seteqP; split=>?/=.
  move=>[x1 P1][x2 P2]<-; exists (val p *: x1); first by exists x1.
  by exists ((1 - val p) *: x2)=>//; exists x2.
move=>[?][x1 P1]<-[?][x2 P2]<-<-.
by exists x1=>//; exists x2.
Qed.

End ConvFsem.

HB.lock
Definition refine_cmd u1 u2 := (fsem u1 `<=` conv (fsem u2))%classic.
Infix "<=c" := refine_cmd (at level 70).

Lemma refine_cmd_trans : 
  forall a b c, a <=c b -> b <=c c -> a <=c c.
Proof. 
rewrite refine_cmd.unlock; move=>a b c.
move=>/conv_le_hom + /conv_le_hom; rewrite !conv_idem=>P1 P2.
apply(subset_trans (B := conv (fsem a))); first by apply/conv_le.
move: P1 P2; apply: subset_trans.
Qed.
Lemma refine_cmd_refl : forall a, a <=c a.
Proof. by rewrite refine_cmd.unlock=>a; apply/conv_le. Qed.
Hint Extern 0 (refine_cmd _ _) => (apply refine_cmd_refl) : core.

(* Lemma refine_cmd_anti : forall a b, a <=c b -> b <=c a -> a =c b.
Proof. by move=>a b; rewrite eq_fsem.unlock refine_cmd.unlock eqEsubset. Qed. *)
Lemma eq_fsem_refine : forall a b, a =c b -> (a <=c b /\ (b <=c a)).
Proof.
by move=>a b; rewrite eq_fsem.unlock refine_cmd.unlock=>->; split; apply/conv_le.
Qed.

Add Parametric Relation : cmd_ refine_cmd
  reflexivity proved by refine_cmd_refl
  transitivity proved by refine_cmd_trans
  as refine_cmd_rel.

(* #[global]
Instance refine_anti_instance : Antisymmetric _ eq_fsem refine_cmd := refine_cmd_anti. *)

(* move *)
Section Refinement.
Require Import Setoid.

(* proposition B.1 (1) *)
Add Parametric Morphism : seqc_
  with signature refine_cmd ==> refine_cmd ==> refine_cmd as refine_cmd_seq.
Proof.
rewrite refine_cmd.unlock; move=>x y P1 w t P2.
rewrite !fsem_seqcE2; apply: (subset_trans (set_compso_le P2 P1)).
rewrite -conv_compso; apply/conv_le.
Qed.

Add Parametric Morphism : seqc_
  with signature eq_fsem ==> eq_fsem ==> refine_cmd as refine_eq_cmd_seq.
Proof. by move=>??/eq_fsem_refine[] + _ ??/eq_fsem_refine[] -> _; move=>->. Qed.

(* proposition B.1 (2) *)
Add Parametric Morphism T (q : qreg T) M : (@cond2_ T q M)
  with signature refine_cmd ==> refine_cmd ==> refine_cmd as refine_cmd_cond2.
Proof.
rewrite refine_cmd.unlock; move=>x y P1 w t P2.
rewrite !fsem_cond2E2 -conv_add; apply/set_add_le;
rewrite -conv_compso conv1.
by apply/(subset_trans (set_compso_ler P1))/conv_le.
by apply/(subset_trans (set_compso_ler P2))/conv_le.
Qed.

Add Parametric Morphism T (q : qreg T) M : (@cond2_ T q M)
  with signature eq_fsem ==> eq_fsem ==> refine_cmd as refine_eq_cmd_cond2.
Proof. by move=>??/eq_fsem_refine[] + _ ??/eq_fsem_refine[] -> _; move=>->. Qed.

(* proposition B.1 (3) *)
(* Add Parametric Morphism T (q : qreg T) M : (@while_ T q M)
  with signature refine_cmd ==> refine_cmd as refine_cmd_while.
Proof.
rewrite refine_cmd.unlock; move=>x y Pxy; rewrite !fsemE => s/=.
move=>[l][]<- Pl.
by move=>[l][]<- Pl; exists l; split=>// n; apply: Pxy.
Qed. *)

Add Parametric Morphism T (q : qreg T) M : (@while_ T q M)
  with signature eq_fsem ==> refine_cmd as refine_eq_cmd_while.
Proof.
move=>x y Pxy; rewrite refine_cmd.unlock.
apply: (subset_trans _ (@conv_le _ _)).
have: <{[M[q] * x]}> =c <{[M[q] * y]}> by rewrite Pxy.
rewrite eq_fsem.unlock=>->; apply subset_refl.
Qed.

(* proposition B.1 (3) *)
Add Parametric Morphism : nchoice_
  with signature refine_cmd ==> refine_cmd ==> refine_cmd as refine_cmd_nchoice.
Proof. 
rewrite refine_cmd.unlock; move=>x y + w t; rewrite !fsemE=>Pxy Pwt s/=[/Pxy|/Pwt].
all: move=>[F][c][f][P1][P2][P3]->;
  exists F; exists c; exists f; do ! split=>//;
  by move=>i; rewrite inE/=; move: (P3 i); rewrite inE; auto.
Qed.

Add Parametric Morphism : nchoice_
  with signature eq_fsem ==> eq_fsem ==> refine_cmd as refine_eq_cmd_nchoice.
Proof. by move=>??/eq_fsem_refine[] + _ ??/eq_fsem_refine[] -> _; move=>->. Qed.

(* proposition B.2 (2) *)
Add Parametric Morphism p : (pchoice_ p)
  with signature refine_cmd ==> refine_cmd ==> refine_cmd as refine_cmd_pchoice.
Proof.
rewrite refine_cmd.unlock; move=>x y P1 w t P2.
rewrite !fsem_pchoiceE2 -conv_add; apply/set_add_le;
by rewrite conv_scale; apply set_scale_le.
Qed.

Add Parametric Morphism p : (pchoice_ p)
  with signature eq_fsem ==> eq_fsem ==> refine_cmd as refine_eq_cmd_pchoice.
Proof. by move=>??/eq_fsem_refine[] + _ ??/eq_fsem_refine[] -> _; move=>->. Qed.

(* proposition B.1 (1) : refinement law: sequential *)
Lemma refine_seqcl c1 c2 c :
  c1 <=c c2 -> <{[ c1 ;; c ]}> <=c <{[ c2 ;; c ]}>.
Proof. by move=>->. Qed.

Lemma refine_seqcr c1 c2 c :
  c1 <=c c2 -> <{[ c ;; c1 ]}> <=c <{[ c ;; c2 ]}>.
Proof. by move=>->. Qed.

Lemma refine_seqc c1 c2 d1 d2 :
  c1 <=c c2 -> d1 <=c d2 -> <{[ c1 ;; d1 ]}> <=c <{[ c2 ;; d2 ]}>.
Proof. by move=>->->. Qed.

(* proposition B.1 (2) : refinement law: if statement *)
Lemma refine_ifG T F (q : qreg T) (M : 'QM(F;'Ht T)) (f g : F -> cmd_) : 
  (forall i, f i <=c g i) ->
  <{[ If M[q] = i then f i fI ]}> <=c <{[ If M[q] = i then g i fI ]}>.
Proof.
rewrite refine_cmd.unlock=>Pi.
rewrite !fsem_condE2 -conv_sum; apply/set_sum_le=>i _.
rewrite -conv_compso conv1; apply/(subset_trans _ (@conv_le _ _)).
by apply/set_compso_ler.
Qed.

Lemma refine_ifl T (q : qreg T) M c1 c2 c :
  c1 <=c c2 -> 
  <{[ c1 ◁ M[q] ▷ c ]}> <=c <{[ c2 ◁ M[q] ▷ c ]}>.
Proof. by move=>->. Qed.

Lemma refine_ifr T (q : qreg T) M c1 c2 c :
  c1 <=c c2 -> 
  <{[ c ◁ M[q] ▷ c1 ]}> <=c <{[ c ◁ M[q] ▷ c2 ]}>.
Proof. by move=>->. Qed.

Lemma refine_if T (q : qreg T) M c1 c2 d1 d2 :
  c1 <=c c2 -> d1 <=c d2 -> 
  <{[ c1 ◁ M[q] ▷ d1 ]}> <=c <{[ c2 ◁ M[q] ▷ d2 ]}>.
Proof. by move=>->->. Qed.

(* proposition B.1 (3) *)
(* Lemma refine_while T (q : qreg T) M c1 c2 :
  c1 <=c c2 -> <{[ M[q] * c1 ]}> <=c <{[ M[q] * c2 ]}>.
Proof. by move=>->. Qed. *)

(* proposition B.1 (3) : refinement law: nondeterministic choice *)
Lemma refine_nchoicel c1 c2 c :
  c1 <=c c2 -> <{[ c1 ⊔ c ]}> <=c <{[ c2 ⊔ c ]}>.
Proof. by move=>->. Qed.

Lemma refine_nchoicer c1 c2 c :
  c1 <=c c2 -> <{[ c ⊔ c1 ]}> <=c <{[ c ⊔ c2 ]}>.
Proof. by move=>->. Qed.

Lemma refine_nchoice c1 c2 d1 d2 :
  c1 <=c c2 -> d1 <=c d2 -> <{[ c1 ⊔ d1 ]}> <=c <{[ c2 ⊔ d2 ]}>.
Proof. by move=>->->. Qed.

(* proposition B.2 (2) : refinement law: probabilistic choice *)
Lemma refine_pchoicel p c1 c2 c :
  c1 <=c c2 -> <{[ c1 ⊔_(p) c ]}> <=c <{[ c2 ⊔_(p) c ]}>.
Proof. by move=>->. Qed.

Lemma refine_pchoicer p c1 c2 c :
  c1 <=c c2 -> <{[ c ⊔_(p) c1 ]}> <=c <{[ c ⊔_(p) c2 ]}>.
Proof. by move=>->. Qed.

Lemma refine_pchoice p c1 c2 d1 d2 :
  c1 <=c c2 -> d1 <=c d2 -> <{[ c1 ⊔_(p) d1 ]}> <=c <{[ c2 ⊔_(p) d2 ]}>.
Proof. by move=>->->. Qed.

(* proposition B.2 (1) : refinement law: probabilistic refine nondeterministic *)
Lemma prop_7_3_1 p c1 c2 :
  <{[ c1 ⊔_(p) c2 ]}> <=c <{[ c1 ⊔ c2 ]}>.
Proof.
rewrite refine_cmd.unlock=>x; rewrite !fsemE/==>[[x1]P1[x2]P2<-].
exists bool. exists (fun b=> if b then (val p) else 1 - (val p)).
exists (fun b=>if b then x1 else x2).
do ! split.
by case; move: (projT2 p)=>// /andP; rewrite subr_ge0 lerBlDl lerDr=>[[] -> ->].
by rewrite big_bool/= addrC subrK.
by case; rewrite inE/=; [left | right].
by rewrite big_bool/=.
Qed.

(* proposition B.2 (3) : refinement law: measurement *)
Lemma prop_7_3_3 T (x : 'QReg[T]) (M : 'QM) c :
  <{[ '[ M[x] ] ;; c ]}> <=c <{[ c ◁ M[x] ▷ c ]}>.
Proof.
rewrite refine_cmd.unlock !fsemE !image2_set1=>y/= [z Pz <-].
exists unit; exists (fun=>1); exists (fun=> z :o 
  (formso (liftf_lf (tf2f x x (M true))) + formso (liftf_lf (tf2f x x (M false))))).
do ! split.
by rewrite ler01 lexx.
by rewrite sumr_const card_unit.
by rewrite inE/=; exists z=>//; exists z=>//=; rewrite comp_soDr.
by rewrite sumr_const scale1r card_unit mulr1n !comp_so1l comp_soDr.
Qed.

(* proposition B.2 (4) : refinement law: quantum choice *)
Lemma prop_7_3_4 T (x : 'QReg[T]) (phi : 'NS) (M : 'QM) c0 c1 :
  <{[ [x] := phi ;; ([x] := phi ;; c0) ◁ M[x] ▷ ([x] := phi ;; c1) ]}> 
    <=c <{[ [x] := phi ;; (c0 ⊔ c1) ]}>.
Proof.
rewrite refine_cmd.unlock fsem_seqcE2 fsem_cond2E2 !fsem_seqcE2 
  fsemE set_compsoxDr -!set_compsoA 4!(set_compsoxr, image2_set1)
  4![in X in _ + X](set_compsoxr, image2_set1).
pose s0 := \Tr (formso (tf2f x x (M false)) [> tv2v x phi; tv2v x phi <]).
pose s1 := \Tr (formso (tf2f x x (M true)) [> tv2v x phi; tv2v x phi <]).
have -> : liftfso (initialso (tv2v x phi))
  :o (formso (liftf_lf (tf2f x x (M false)))
      :o liftfso (initialso (tv2v x phi))) = 
      s0 *: liftfso (initialso (tv2v x phi)).
  rewrite -liftfso_formso -!liftfso_comp -linearZ/=; f_equal.
  apply/superopP=>r; rewrite 2!soE [RHS]soE !initialsoE scalerA; f_equal.
  by rewrite mulrC !linearZ/=.
have -> : liftfso (initialso (tv2v x phi))
  :o (formso (liftf_lf (tf2f x x (M true)))
      :o liftfso (initialso (tv2v x phi))) = 
      s1 *: liftfso (initialso (tv2v x phi)).
  rewrite -liftfso_formso -!liftfso_comp -linearZ/=; f_equal.
  apply/superopP=>r; rewrite 2!soE [RHS]soE !initialsoE scalerA; f_equal.
  by rewrite mulrC !linearZ/=.
rewrite -!set_scalex -!set_compsoZr !set_compsoZl -set_compsoxDr.
rewrite -conv_compso conv1; 
apply/(subset_trans _ (@conv_le _ _))/set_compso_ler.
have P1: 0 <= s0 by rewrite /s0 psdf_trlf.
have P2: 0 <= s1 by rewrite /s1 psdf_trlf.
have P3: s0 = 1 - s1.
apply/eqP; rewrite eq_sym subr_eq addrC /s0 /s1.
rewrite !formsoE lftraceC [X in _ + X]lftraceC !comp_lfunA
  -linearD/= -linearDl/= !tf2f_adj !tf2f_comp -linearD/=.
move: (is_trpresv M); rewrite /trace_presv big_bool/= addrC=>/eqP->.
by rewrite tf2f1 comp_lfun1l outp_trlf ns_dot.
have P4: 0 <= s0 <= 1 by rewrite P1/= P3 gerBl.
move: (prop_7_3_1 (exist _ s0 P4) c0 c1).
rewrite refine_cmd.unlock; apply: subset_trans.
by rewrite fsem_pchoiceE2/= P3 subKr.
Qed.

End Refinement.

(*****************************************************************************)
(*                                 Automation                                *)
(*****************************************************************************)
(* solving cmd_expose *)

Module NonDeterministicAuto.
Export CircuitAuto.

HB.lock Definition cmd_var_disj_lock := cmd_var_disj.
Lemma cmd_var_disj_lockE : cmd_var_disj = cmd_var_disj_lock.
Proof. by rewrite cmd_var_disj_lock.unlock. Qed.
HB.lock Definition cmd_disj_lock := cmd_disj.
Lemma cmd_disj_lockE : cmd_disj = cmd_disj_lock.
Proof. by rewrite cmd_disj_lock.unlock. Qed.
HB.lock Definition cmd_ucmd_disj_lock := cmd_ucmd_disj.
Lemma cmd_ucmd_disj_lockE : cmd_ucmd_disj = cmd_ucmd_disj_lock.
Proof. by rewrite cmd_ucmd_disj_lock.unlock. Qed.
HB.lock Definition no_nchoice_lock := no_nchoice_.
Lemma no_nchoice_lockE : no_nchoice_ = no_nchoice_lock.
Proof. by rewrite no_nchoice_lock.unlock. Qed.

Lemma cmd_var_disj_lock_skip T (x : qreg T) : cmd_var_disj_lock x skip_.
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_abort T (x : qreg T) : cmd_var_disj_lock x abort_.
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_init T1 T2 (x1 : qreg T1) (x2 : qreg T2) v : 
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 (init_ x2 v).
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_circuit T (x : qreg T) u : 
  ucmd_var_disj_lock x u -> cmd_var_disj_lock x (circuit_ u).
Proof. by rewrite -cmd_var_disj_lockE -ucmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_cond2 T1 T2 (x1 : qreg T1) (x2 : qreg T2) M c0 c1 :
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 c0 -> cmd_var_disj_lock x1 c1 ->
  cmd_var_disj_lock x1 (cond2_ x2 M c0 c1).
Proof. by rewrite -cmd_var_disj_lockE cond2_.unlock/==>->??; apply/forallP; case. Qed.

Lemma cmd_var_disj_lock_cond T1 T2 (F : finType) 
  (x1 : qreg T1) (x2 : qreg T2) M (f : F -> cmd_) :
  disjoint_qreg x1 x2 -> (forall i, cmd_var_disj_lock x1 (f i)) ->
  cmd_var_disj_lock x1 (cond_ x2 M f).
Proof. by rewrite -cmd_var_disj_lockE/==>->?; apply/forallP. Qed.

Lemma cmd_var_disj_lock_sequ T (x : qreg T) c1 c2 :
  cmd_var_disj_lock x c1 -> cmd_var_disj_lock x c2 ->
  cmd_var_disj_lock x (seqc_ c1 c2).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_while T1 T2 (x1 : qreg T1) (x2 : qreg T2) M c :
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 c ->
  cmd_var_disj_lock x1 (while_ x2 M c).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_nchoice T (x : qreg T) c1 c2 :
  cmd_var_disj_lock x c1 -> cmd_var_disj_lock x c2 ->
  cmd_var_disj_lock x (nchoice_ c1 c2).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_pchoice T (x : qreg T) p c1 c2 :
  cmd_var_disj_lock x c1 -> cmd_var_disj_lock x c2 ->
  cmd_var_disj_lock x (pchoice_ p c1 c2).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_if T (x : qreg T) b u0 u1 :
  cmd_var_disj_lock x u0 -> cmd_var_disj_lock x u1 ->
    cmd_var_disj_lock x (if b then u0 else u1).
Proof. by case: b. Qed.

Ltac tac_cmd_var_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_var_disj_lock ?x ?y) |- is_true (cmd_var_disj_lock ?x ?y) ] => 
          apply H
  | [ |- is_true (cmd_var_disj_lock _ abort_)] => 
          apply/cmd_var_disj_lock_abort
  | [ |- is_true (cmd_var_disj_lock _ skip_)] => 
          apply/cmd_var_disj_lock_skip
  | [ |- is_true (cmd_var_disj_lock _ (init_ _ _))] => 
          apply/cmd_var_disj_lock_init
  | [ |- is_true (cmd_var_disj_lock _ (circuit_ _))] => 
          apply/cmd_var_disj_lock_circuit
  | [ |- is_true (cmd_var_disj_lock _ (seqc_ _ _))] => 
          apply/cmd_var_disj_lock_sequ
  | [ |- is_true (cmd_var_disj_lock _ (cond2_ _ _ _ _))] => 
          apply/cmd_var_disj_lock_cond2
  | [ |- is_true (cmd_var_disj_lock _ (cond_ _ _ _))] => 
          apply/cmd_var_disj_lock_cond
  | [ |- is_true (cmd_var_disj_lock _ (while_ _ _ _))] => 
          apply/cmd_var_disj_lock_while
  | [ |- is_true (cmd_var_disj_lock _ (nchoice_ _ _))] => 
          apply/cmd_var_disj_lock_nchoice
  | [ |- is_true (cmd_var_disj_lock _ (pchoice_ _ _ _))] => 
          apply/cmd_var_disj_lock_pchoice
  | [ |- is_true (cmd_var_disj_lock _ (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/cmd_var_disj_lock_if
  | [ |- is_true (disjoint_qreg _ _) ] => QRegAuto.tac_expose
  | [ |- is_true (ucmd_var_disj_lock _ _) ] => tac_ucmd_var_disj
end.

Lemma cmd_ucmd_disj_lock_uskip c : cmd_ucmd_disj_lock uskip_ c.
Proof. by rewrite -cmd_ucmd_disj_lockE. Qed.

Lemma cmd_ucmd_disj_lock_unitary T (x : qreg T) U c : 
  cmd_var_disj_lock x c -> cmd_ucmd_disj_lock (unitary_ x U) c.
Proof. by rewrite -cmd_ucmd_disj_lockE -cmd_var_disj_lockE. Qed.

Lemma cmd_ucmd_disj_lock_sequ u1 u2 c : 
  cmd_ucmd_disj_lock u1 c -> cmd_ucmd_disj_lock u2 c ->
    cmd_ucmd_disj_lock (sequ_ u1 u2) c.
Proof. by rewrite -cmd_ucmd_disj_lockE/==>->->. Qed.

Lemma cmd_ucmd_disj_lock_qcond2 (x : qreg Bool) phi u0 u1 c : 
  cmd_var_disj_lock x c -> cmd_ucmd_disj_lock u0 c -> cmd_ucmd_disj_lock u1 c ->
    cmd_ucmd_disj_lock (qcond2_ x phi u0 u1) c.
Proof.
rewrite -cmd_ucmd_disj_lockE/= qcond2_.unlock/= -cmd_var_disj_lockE=>->??; 
by apply/forallP; case.
Qed.

Lemma cmd_ucmd_disj_lock_qcond T (F : finType) (x : qreg T) phi (f : F -> ucmd_) c : 
  cmd_var_disj_lock x c -> (forall i, cmd_ucmd_disj_lock (f i) c) -> 
    cmd_ucmd_disj_lock (qcond_ x phi f) c.
Proof. by rewrite -cmd_ucmd_disj_lockE/= -cmd_var_disj_lockE=>->?; apply/forallP. Qed.

Lemma cmd_ucmd_disj_lock_if b u0 u1 c :
  cmd_ucmd_disj_lock u0 c -> cmd_ucmd_disj_lock u1 c ->
    cmd_ucmd_disj_lock (if b then u0 else u1) c.
Proof. by case: b. Qed.

Ltac tac_cmd_ucmd_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_ucmd_disj_lock ?x ?y) |- is_true (cmd_ucmd_disj_lock ?x ?y) ] => 
          apply H
  | [ |- is_true (cmd_ucmd_disj_lock uskip_ _)] => 
          apply/cmd_ucmd_disj_lock_uskip
  | [ |- is_true (cmd_ucmd_disj_lock (unitary_ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_unitary
  | [ |- is_true (cmd_ucmd_disj_lock (sequ_ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_sequ
  | [ |- is_true (cmd_ucmd_disj_lock (qcond2_ _ _ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_qcond2
  | [ |- is_true (cmd_ucmd_disj_lock (qcond_ _ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_qcond
  | [ |- is_true (cmd_ucmd_disj_lock (if _ then _ else _) _) ] =>
          rewrite ?eqxx/=; try apply/cmd_ucmd_disj_lock_if
  | [ |- is_true (cmd_var_disj_lock _ _) ] => tac_cmd_var_disj
end.

Lemma cmd_disj_lock_abort c : cmd_disj_lock abort_ c.
Proof. by rewrite -cmd_disj_lockE. Qed.

Lemma cmd_disj_lock_skip c : cmd_disj_lock skip_ c.
Proof. by rewrite -cmd_disj_lockE. Qed.

Lemma cmd_disj_lock_init T (x : qreg T) v c : 
  cmd_var_disj_lock x c -> cmd_disj_lock (init_ x v) c.
Proof. by rewrite -cmd_disj_lockE/= -cmd_var_disj_lockE. Qed.

Lemma cmd_disj_lock_circuit u c : 
  cmd_ucmd_disj_lock u c -> cmd_disj_lock (circuit_ u) c.
Proof. by rewrite -cmd_disj_lockE -cmd_ucmd_disj_lockE. Qed.

Lemma cmd_disj_lock_cond2 T (x : qreg T) M c0 c1 c :
  cmd_var_disj_lock x c -> cmd_disj_lock c0 c -> cmd_disj_lock c1 c ->
    cmd_disj_lock (cond2_ x M c0 c1) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE cond2_.unlock/==>->??; apply/forallP; case. Qed.

Lemma cmd_disj_lock_cond T (F : finType) (x : qreg T) M (f : F -> cmd_) c :
  cmd_var_disj_lock x c -> (forall i, cmd_disj_lock (f i) c) ->
    cmd_disj_lock (cond_ x M f) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE/==>->?; apply/forallP. Qed.

Lemma cmd_disj_lock_sequ c1 c2 c :
  cmd_disj_lock c1 c -> cmd_disj_lock c2 c ->
  cmd_disj_lock (seqc_ c1 c2) c.
Proof. by rewrite -cmd_disj_lockE /==>->->. Qed.

Lemma cmd_disj_lock_while T (x : qreg T) M c1 c :
  cmd_var_disj_lock x c -> cmd_disj_lock c1 c ->
  cmd_disj_lock (while_ x M c1) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE/==>->->. Qed.

Lemma cmd_disj_lock_nchoice c1 c2 c :
  cmd_disj_lock c1 c -> cmd_disj_lock c2 c ->
  cmd_disj_lock (nchoice_ c1 c2) c.
Proof. by rewrite -cmd_disj_lockE /==>->->. Qed.

Lemma cmd_disj_lock_pchoice p c1 c2 c :
  cmd_disj_lock c1 c -> cmd_disj_lock c2 c ->
  cmd_disj_lock (pchoice_ p c1 c2) c.
Proof. by rewrite -cmd_disj_lockE /==>->->. Qed.

Lemma cmd_disj_lock_if b c0 c1 c :
  cmd_disj_lock c0 c -> cmd_disj_lock c1 c ->
    cmd_disj_lock (if b then c0 else c1) c.
Proof. by case: b. Qed.

Lemma cmd_disjC c1 c2 : cmd_disj c1 c2 = cmd_disj c2 c1.
Proof.
elim: c1 c2=>/=.
- elim=>//=[|?<-?<-//|????? IH|?<-?<-//|??<-?<-//].
  - by elim=>//=[?<-?<-//|????? IH]; symmetry; apply/forallP=>?. 
  - by symmetry; apply/forallP.
- elim=>//=[|?<-?<-//|????? IH|?<-?<-//|??<-?<-//].
  - by elim=>//=[?<-?<-//|????? IH]; symmetry; apply/forallP=>?. 
  - by symmetry; apply/forallP.
- move=>???; elim=>//=[???||?->?->//|????? IH|???? <-|?->?->//|??->?->//].
  - by rewrite QRegAuto.disjoint_qregC.
  - elim=>//=[???|?->?->//|????? IH];
    rewrite QRegAuto.disjoint_qregC//; f_equal;
    by under eq_forallb do rewrite IH.
  - rewrite QRegAuto.disjoint_qregC; f_equal;
    by under eq_forallb do rewrite IH.
  - by rewrite QRegAuto.disjoint_qregC.
- move=>u; elim=>//=; last move=>?.
  - by elim: u=>//=[?->?->//|????? IH]; apply/forallP.
  - by elim: u=>//=[?->?->//|????? IH]; apply/forallP.
  - move=>???; elim: u=>//=[???|?->?->//|????? IH]; 
    by rewrite QRegAuto.disjoint_qregC//; under eq_forallb do rewrite IH.
  - elim: u=>//=.
    - by elim=>//=[?->?->|????? IH]; rewrite ?andbb//; symmetry; apply/forallP.
    - move=>???; elim=>//=[???|?<-?<-//|????? IH];
      by rewrite QRegAuto.disjoint_qregC//; under eq_forallb do rewrite IH.
    - move=>?+?+u; move=>->->; elim: u=>//=[?<-?<-|????? IH];
      by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
    - move=>????? IH; elim=>//=.
      - by apply/forallP=>?; rewrite IH.
      - by move=>???; rewrite QRegAuto.disjoint_qregC; under eq_forallb do rewrite IH.
      - by move=>?<-?<-; rewrite andbACA forallb_and; under eq_forallb do rewrite IH/= -!IH.
      - move=>????? IH1; rewrite QRegAuto.disjoint_qregC -!andbA; f_equal.
        apply/eqb_iff; split.
          move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
          by move: (P2 i); rewrite IH/==>/andP[].
          rewrite -IH1; apply/andP; split=>//; apply/forallP=>j.
          by move: (P2 j); rewrite !IH/==>/andP[] _ /forallP.
        move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
        by move: (P2 i); rewrite -IH1/==>/andP[].
        rewrite IH/=; apply/andP; split=>//; apply/forallP=>j.
        by move: (P2 j); rewrite -IH1 -IH/==>/andP[] _ /forallP.
  1,4,5: move=>?<-?<-; elim: u=>//=[?->?->|????? IH];
    by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
  - move=>????? IH; under eq_forallb do rewrite -IH; clear.
    elim: u=>//=.
    - by symmetry; apply/forallP.
    - by move=>???; rewrite QRegAuto.disjoint_qregC.
    - by move=>?->?->; rewrite andbACA forallb_and.
    - move=>????? IH; rewrite QRegAuto.disjoint_qregC -!andbA; f_equal.
      apply/eqb_iff; split.
        move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
        by move: (P2 i); rewrite IH/==>/andP[].
        rewrite P1/=; apply/forallP=>j.
        by move: (P2 j); rewrite !IH/==>/andP[] _ /forallP.
      move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
      by move: (P2 i)=>/andP[].
      rewrite IH/=; apply/andP; split=>//; apply/forallP=>j.
      by move: (P2 j)=>/andP[] _ /forallP.
  - move=>????<-; elim: u=>//=.
    - by move=>???; rewrite QRegAuto.disjoint_qregC.
    - by move=>?->?->; rewrite andbACA.
    - by move=>????? IH; rewrite andbACA QRegAuto.disjoint_qregC forallb_and;
      under eq_forallb do rewrite IH.
- move=>? IH1? IH2 c2; rewrite IH1 IH2; elim: c2=>//=; last move=>?.
  - elim=>//=[?<-?<-|????? IH];
    by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
  1,4,5: by move=>?<-?<-; rewrite !andbA; f_equal; rewrite -!andbA; f_equal; rewrite andbC.
  - by move=>????? IH; rewrite andbACA forallb_and; under eq_forallb do rewrite IH.
  - by move=>???? IH; rewrite andbACA IH.
- move=>????? IH; elim=>//=; last move=>?.
  - by apply/forallP=>?; rewrite IH.
  - by apply/forallP=>?; rewrite IH.
  - by move=>???; rewrite QRegAuto.disjoint_qregC; under eq_forallb do rewrite IH.
  - elim=>//=.
    - by apply/forallP=>?; rewrite IH.
    - by move=>???; rewrite QRegAuto.disjoint_qregC; under eq_forallb do rewrite IH.
    - move=>?<-?<-; rewrite andbACA forallb_and; under eq_forallb do rewrite IH/=;
      by under [in RHS]eq_forallb do rewrite !IH.
    - move=>????? IH1; rewrite QRegAuto.disjoint_qregC -!andbA; f_equal.
      apply/eqb_iff; split.
        move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
        by move: (P2 i); rewrite IH/==>/andP[].
        rewrite -IH1; apply/andP; split=>//; apply/forallP=>j.
        by move: (P2 j); rewrite !IH/==>/andP[] _ /forallP.
      move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
      by move: (P2 i); rewrite -IH1/==>/andP[].
      rewrite IH/=; apply/andP; split=>//; apply/forallP=>j.
      by move: (P2 j); rewrite -IH1/==>/andP[] _ /forallP/(_ i); rewrite IH.
  1,4,5: move=>?<-?<-; rewrite andbACA forallb_and; f_equal;
    by under eq_forallb do rewrite IH/= -!IH.
  - move=>????? IH1; rewrite QRegAuto.disjoint_qregC -!andbA; f_equal.
    apply/eqb_iff; split.
      move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
      by move: (P2 i); rewrite IH/==>/andP[].
      rewrite -IH1; apply/andP; split=>//; apply/forallP=>j.
      by move: (P2 j); rewrite !IH/==>/andP[] _ /forallP.
    move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
    by move: (P2 i); rewrite -IH1/==>/andP[].
    rewrite IH/=; apply/andP; split=>//; apply/forallP=>j.
    by move: (P2 j); rewrite -IH1 -IH/==>/andP[] _ /forallP.
  - move=>????<-; rewrite andbACA QRegAuto.disjoint_qregC forallb_and; f_equal.
    by under eq_forallb do rewrite IH/= -IH.
- move=>???? IH; elim=>//=; last move=>?.
  - by move=>???; rewrite QRegAuto.disjoint_qregC IH.
  - elim=>//=.
    - by move=>???; rewrite QRegAuto.disjoint_qregC IH.
    - by move=>?<-?<-; rewrite andbACA !IH.
    - move=>????? IH1; rewrite QRegAuto.disjoint_qregC IH/= andbACA forallb_and;
      by under [in RHS]eq_forallb do rewrite -IH1 IH.
  1,4,5: by move=>?<-?<-; rewrite andbACA; f_equal; rewrite !IH/=.
  - move=>????? IH1; rewrite IH/= andbACA QRegAuto.disjoint_qregC; f_equal.
    by rewrite forallb_and; under eq_forallb do rewrite -IH IH1.
  - by move=>????<-; rewrite !IH/= andbACA QRegAuto.disjoint_qregC.
- move=>? IH1? IH2 c2; rewrite IH1 IH2; elim: c2=>//=; last move=>?.
  - elim=>//=[?<-?<-|????? IH];
    by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
  1,4,5: by move=>?<-?<-; rewrite !andbA; f_equal; rewrite -!andbA; f_equal; rewrite andbC.
  - by move=>????? IH; rewrite andbACA forallb_and; under eq_forallb do rewrite IH.
  - by move=>???? IH; rewrite andbACA IH.
- move=>?? IH1? IH2 c2; rewrite IH1 IH2; elim: c2=>//=; last move=>?.
  - elim=>//=[?<-?<-|????? IH];
    by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
  1,4,5: by move=>?<-?<-; rewrite !andbA; f_equal; rewrite -!andbA; f_equal; rewrite andbC.
  - by move=>????? IH; rewrite andbACA forallb_and; under eq_forallb do rewrite IH.
  - by move=>???? IH; rewrite andbACA IH.
Qed.

Lemma cmd_disj_lockC c1 c2 : cmd_disj_lock c1 c2 = cmd_disj_lock c2 c1.
Proof. by rewrite -cmd_disj_lockE cmd_disjC. Qed.

Ltac tac_cmd_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_disj_lock ?x ?y) |- is_true (cmd_disj_lock ?x ?y)] => 
          apply H
  | [ H : is_true (cmd_disj_lock ?x ?y) |- is_true (cmd_disj_lock ?y ?x)] => 
          rewrite cmd_disj_lockC; apply H
  | [ |- is_true (cmd_disj_lock abort_ _)] => 
          apply/cmd_disj_lock_abort
  | [ |- is_true (cmd_disj_lock skip_ _)] => 
          apply/cmd_disj_lock_skip
  | [ |- is_true (cmd_disj_lock (init_ _ _) _)] => 
          apply/cmd_disj_lock_init
  | [ |- is_true (cmd_disj_lock (circuit_ _) _)] => 
          apply/cmd_disj_lock_circuit
  | [ |- is_true (cmd_disj_lock (seqc_ _ _) _)] => 
          apply/cmd_disj_lock_sequ
  | [ |- is_true (cmd_disj_lock (cond2_ _ _ _ _) _)] => 
          apply/cmd_disj_lock_cond2
  | [ |- is_true (cmd_disj_lock (cond_ _ _ _) _)] => 
          apply/cmd_disj_lock_cond
  | [ |- is_true (cmd_disj_lock (while_ _ _ _) _)] => 
          apply/cmd_disj_lock_while
  | [ |- is_true (cmd_disj_lock (nchoice_ _ _) _)] => 
          apply/cmd_disj_lock_nchoice
  | [ |- is_true (cmd_disj_lock (pchoice_ _ _ _) _)] => 
          apply/cmd_disj_lock_pchoice
  | [ |- is_true (cmd_disj_lock (if _ then _ else _) _) ] =>
          rewrite ?eqxx/=; try apply/cmd_disj_lock_if
  | [ |- is_true (cmd_var_disj_lock _ _) ] => tac_cmd_var_disj
  | [ |- is_true (cmd_ucmd_disj_lock _ _) ] => tac_cmd_ucmd_disj
end.

(* no nchoice *)
Lemma no_nchoice_lock_abort : no_nchoice_lock abort_.
Proof. by rewrite -no_nchoice_lockE. Qed.

Lemma no_nchoice_lock_skip : no_nchoice_lock skip_.
Proof. by rewrite -no_nchoice_lockE. Qed.

Lemma no_nchoice_lock_init T x v : no_nchoice_lock (@init_ T x v).
Proof. by rewrite -no_nchoice_lockE/=. Qed.

Lemma no_nchoice_lock_circuit u : no_nchoice_lock (circuit_ u).
Proof. by rewrite -no_nchoice_lockE. Qed.

Lemma no_nchoice_lock_cond2 T x M c0 c1 :
  no_nchoice_lock c0 -> no_nchoice_lock c1 ->
    no_nchoice_lock (@cond2_ T x M c0 c1).
Proof. by rewrite -no_nchoice_lockE cond2_.unlock/==>??; apply/forallP; case. Qed.

Lemma no_nchoice_lock_cond T (F : finType) (x : qreg T) M (f : F -> cmd_) :
  (forall i, no_nchoice_lock (f i)) -> no_nchoice_lock (cond_ x M f).
Proof. by rewrite -no_nchoice_lockE /==>?; apply/forallP. Qed.

Lemma no_nchoice_lock_sequ c1 c2 :
  no_nchoice_lock c1 -> no_nchoice_lock c2 ->
  no_nchoice_lock (seqc_ c1 c2).
Proof. by rewrite -no_nchoice_lockE /==>->->. Qed.

Lemma no_nchoice_lock_while T (x : qreg T) M c1 :
  no_nchoice_lock c1 -> no_nchoice_lock (while_ x M c1).
Proof. by rewrite -no_nchoice_lockE/==>->. Qed.

Lemma no_nchoice_lock_pchoice p c1 c2 :
  no_nchoice_lock c1 -> no_nchoice_lock c2 ->
  no_nchoice_lock (pchoice_ p c1 c2).
Proof. by rewrite -no_nchoice_lockE /==>->->. Qed.

Lemma no_nchoice_lock_if b c0 c1 :
  no_nchoice_lock c0 -> no_nchoice_lock c1 ->
    no_nchoice_lock (if b then c0 else c1).
Proof. by case: b. Qed.

Ltac tac_no_nchoice := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (no_nchoice_lock ?x) |- is_true (no_nchoice_lock ?x)] => 
          apply H
  | [ |- is_true (no_nchoice_lock abort_)] => 
          apply/no_nchoice_lock_abort
  | [ |- is_true (no_nchoice_lock skip_)] => 
          apply/no_nchoice_lock_skip
  | [ |- is_true (no_nchoice_lock (init_ _ _))] => 
          apply/no_nchoice_lock_init
  | [ |- is_true (no_nchoice_lock (circuit_ _))] => 
          apply/no_nchoice_lock_circuit
  | [ |- is_true (no_nchoice_lock (seqc_ _ _))] => 
          apply/no_nchoice_lock_sequ
  | [ |- is_true (no_nchoice_lock (cond2_ _ _ _ _))] => 
          apply/no_nchoice_lock_cond2
  | [ |- is_true (no_nchoice_lock (cond_ _ _ _))] => 
          apply/no_nchoice_lock_cond
  | [ |- is_true (no_nchoice_lock (while_ _ _ _))] => 
          apply/no_nchoice_lock_while
  | [ |- is_true (no_nchoice_lock (pchoice_ _ _ _))] => 
          apply/no_nchoice_lock_pchoice
  | [ |- is_true (no_nchoice_lock (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/no_nchoice_lock_if
end.

Ltac tac_qwhile_auto := rewrite /cmd_expose ?ucmd_var_disj_lockE
  ?ucmd_disj_lockE ?ucmd_var_subset_lockE ?ucmd_wf_lockE ?no_nchoice_lockE
  ?cmd_var_disj_lockE ?cmd_disj_lockE ?cmd_ucmd_disj_lockE;
  rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=;
  match goal with
  | [ H : ?x |- ?x ] => apply H
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ |- is_true (ucmd_var_disj_lock _ _)] => tac_ucmd_var_disj
  | [ |- is_true (disjoint_qreg _ _)] => QRegAuto.tac_expose
  | [ |- is_true (ucmd_disj_lock _ _)] => tac_ucmd_disj
  | [ |- is_true (ucmd_var_subset_lock _ _)] => tac_ucmd_var_subset
  | [ |- is_true (ucmd_wf_lock _)] => tac_ucmd_wf
  | [ |- is_true (valid_qreg _)] => QRegAuto.tac_expose
  | [ |- is_true (cmd_var_disj_lock _ _)] => tac_cmd_var_disj
  | [ |- is_true (cmd_disj_lock _ _)] => tac_cmd_disj
  | [ |- is_true (cmd_ucmd_disj_lock _ _)] => tac_cmd_ucmd_disj
  | [ |- is_true (no_nchoice_lock _)] => tac_no_nchoice
  end.

Module Exports.
Global Hint Extern 0 (cmd_expose _) => (tac_qwhile_auto) : typeclass_instances.
End Exports.
End NonDeterministicAuto.
