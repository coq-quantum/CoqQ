(* -------------------------------------------------------------------- *)
(* Change numClosedFieldType to C *)
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import forms spectral.
From mathcomp.analysis Require Import reals boolp classical_sets topology normedtype sequences.
From mathcomp.real_closed Require Import complex.
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra prodvect hermitian tensor cpo mxtopology mxpred mxnorm lfundef.
Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import Vector.InternalTheory.

(******************************************************************************)
(*                 Fundamental Concepts for Quantum Framework                 *)
(* This file gives most of the mathematical objects of quantum computation    *)
(* based on linear function representation, that is, all the things are       *)
(* defined and represented by linear maps 'Hom                                *)
(*                                                                            *)
(*                   \Tr f := trace of f                                      *)
(*                 \Rank f := rank of f                                       *)
(*                    f^⟂ := complement of f, i.e., \1 - f                    *)
(* Predicates on 'End(U) / Structure notation                                 *)
(*     hermlf     'FH      := Hermitian, i.e., f^A = f                        *)
(*     psdlf      'F+      := positive-semidefinite                           *)
(*     denlf      'FD      := partial density operator, psdlf and \Tr f <= 1  *)
(*     den1lf     'FD1     := density operator, psdlf and \Tr f = 1           *)
(*     obslf      'FO      := observable, psdlf and f ⊑ \1                    *)
(*     unitarylf  'FU      := unitary, f^A \o f = \1                          *)
(*     projlf     'FP      := projection, f \o f = \1 & f^A = f               *)
(*     proj1lf    'FP1     := rank 1 projection, projlf & \Rank f = 1         *)
(*        'FH(U), 'FH[H]_S := hermfType over 'End(U) / hermfType over 'F[H]_S *)
(*        [herm of f as g] := T-clone of the hermfType of f                   *)
(*                            structure g.                                    *)
(*             [herm of f] := clone of a canonical structure of               *)
(*                            hermfType on f.                                 *)
(*          same for all predicate above                                      *)
(* -------------------------------------------------------------------------- *)
(*  'SO(U,V), 'SO[H]_(S,T) := type of super-operator ; coercion to 'Hom       *)
(*                      :1 := identity super-operator (= \1)                  *)
(*                  E :o F := composition of super-operator                   *)
(*                            (E :o F)(x) = E(F(x))                           *)
(*                  E o: F := composition of super-operator                   *)
(*                            (E o: F)(x) = F(E(x))                           *)
(*                 E :⊗ F := tensor product of super-operator                *)
(*               krausso f := with (f : F -> 'Hom(U,V))                       *)
(*                            build super-operator E s.t.                     *)
(*                            E x = \sum_i (f i) \o x \o (f i)^A              *)
(*                formso f := with (f : 'Hom(U,V))                            *)
(*                            build super-operator E s.t.                     *)
(*                            E x = f \o x \o f^A                             *)
(*               ifso f br := with (f : F -> 'Hom(U,V))                       *)
(*                                 (br : forall i : F, 'SO(V,W))              *)
(*                            build super-operator E s.t.                     *)
(*                            E x = \sum_i (br i) ((f i) \o x \o (f i)^A)     *)
(*                dualso E := build super-operator E^*o s.t.                  *)
(*                            \Tr (E x \o A) = \Tr (x \o (E^*o A))            *)
(*                            via choi matrix                                 *)
(*    whileso_iter M b D n := with (M : bool -> 'End(U)) (b : bool)           *)
(*                                 (D : 'SO(U)) (n : nat)                     *)
(*                            nth iteration of                                *)
(*                                ifso M (fun i => if i==b then D             *)
(*                                                         else 0)            *)
(*           whileso M b D := lim (whileso_iter M b D)                        *)
(*                            limit exists if trace_nincr M & D is CPTN       *)
(*   Theory between super-operator and choi matrix.                           *)
(*               so2choi E := choi matrix of super-operator E                 *)
(*               choi2so M := super-operator build from choi matrix M         *)
(*                            so2choi (choi2so M) = M                         *)
(*                            choi2so (so2choi E) = E                         *)
(*               krausop E := build the kraus operator of E                   *)
(*                            krausso (krausop E) = E if E is iscp            *)
(* -------------------------------------------------------------------------- *)
(* Provide U V W : chsType, F : finType                                       *)
(*   ponbasis (f : F -> U) := partial orthonormal basis                       *)
(*                            forall i j : F, [< f i ; f j >] = (i == j)%:R   *)
(*    onbasis (f : F -> U) := ponb & #|F| = Vector.dim U                      *)
(*           trace_nincr f := with (f : F -> 'Hom(U,V))                       *)
(*                            trace nonincreasing, i.e.,                      *)
(*                            \sum_i ((f i)^A \o (f i)) ⊑ \1)%VF              *)
(*           trace_presv f := with (f : F -> 'Hom(U,V))                       *)
(*                            trace preserving, i.e.,                         *)
(*                            (\sum_i ((f i)^A \o (f i)) == \1)%VF            *)
(*                  iscp E == so2choi is psdmx                                *)
(*                            E is completely positive                        *)
(*                  isqo E == so2choi is psdmx && ptrace (so2choi ⊑ 1%:M)     *)
(*                         == iscp E & forall x, 0 ⊑ x -> \Tr (E x) <= \Tr x  *)
(*                            E is completely positive and trace nonincreaing *)
(*                            i.e., E is CPTN                                 *)
(*                  isqc E == so2choi is psdmx && ptrace (so2choi = 1%:M)     *)
(*                         == iscp E & forall x, \Tr (E x) = \Tr x            *)
(*                            E is completely positive and trace perserving   *)
(*                            i.e., E is CPTP                                 *)
(* -------------------------------------------------------------------------- *)
(*             'PONB(F; U) := structure type of ponbasis                      *)
(*                            parital orthnormal basis                        *)
(*          'PONB[H]_(F;S) == 'PONB(F; 'H[H]_S)                               *)
(*        [PONB of f as g] := T-clone of the 'PONB of f                       *)
(*                            structure g.                                    *)
(*             [PONB of f] := clone of a canonical structure of               *)
(*                            'PONB of f                                      *)
(*              'ONB(F; U) := structure type of onbasis                       *)
(*                            orthonormal basis                               *)
(*           'ONB[H]_(F;S) == 'ONB(F; 'H[H]_S)                                *)
(*         [ONB of f as g] := T-clone of the 'ONB of f                        *)
(*                            structure g.                                    *)
(*              [ONB of f] := clone of a canonical structure of               *)
(*                            'ONB of f                                       *)
(*                  'NS(U) := structure type of normalized state              *)
(*                'NS[H]_S == 'NS('H[H]_S)                                    *)
(*          [NS of u as v] := T-clone of the 'NS of u                         *)
(*                            structure v.                                    *)
(*               [NS of u] := clone of a canonical structure of               *)
(*                            'NS of u                                        *)
(*                'CP(U,V) := structure type of completely positive           *)
(*                            super-operator, i.e., iscp                      *)
(*            'CP[H]_(S,T) == 'CP('H[H]_S,'H[H]_T)                            *)
(*          [CP of E as F] := T-clone of the 'CP of E                         *)
(*                            structure F.                                    *)
(*               [CP of E] := clone of a canonical structure of               *)
(*                            'CP of E                                        *)
(*                'QO(U,V) := structure type of quantum operation, i.e.,      *)
(*                            completely positive and trace nonincreaing      *)
(*                            isqo                                            *)
(*            'QO[H]_(S,T) == 'QO('H[H]_S,'H[H]_T)                            *)
(*          [QO of E as F] := T-clone of the 'QO of E                         *)
(*                            structure F.                                    *)
(*               [QO of E] := clone of a canonical structure of               *)
(*                            'QO of E                                        *)
(*                'QC(U,V) := structure type of quantum channel, i.e.,        *)
(*                            completely positive and trace perserving        *)
(*                            isqo                                            *)
(*            'QC[H]_(S,T) == 'QC('H[H]_S,'H[H]_T)                            *)
(*          [QC of E as F] := T-clone of the 'QC of E                         *)
(*                            structure F.                                    *)
(*               [QC of E] := clone of a canonical structure of               *)
(*                            'QC of E                                        *)
(* -------------------------------------------------------------------------- *)
(* Topology / Vector Order                                                    *)
(*   U, 'Hom(U,V), 'SO(U,V) :  finNormedModType, CompleteNormedModule         *)
(*                        U :  hnorm (induced by inner product)               *)
(*                'Hom(U,V) :  trace norm                                     *)
(*                    f ⊑ g := (g - f) \is psdlf                              *)
(*                    E ⊑ F := (F - E) \is iscp                               *)
(*   'FD(U), 'FO(U), 'QO(U) :  forms CPO (complete partial order)             *)
(* -------------------------------------------------------------------------- *)
(* Others:                                                                    *)
(*     Ranking function : define for total correctness of program             *)
(*     cylindrical extension of 'F[H]_S, 'SO[H]_S                             *)
(*         lift_lf, liftso := lift to a larger space                          *)
(*       liftf_lf, liftfso := lift to the global space                        *)
(*     Provide a lot of Canonical Structure, e.g.,                            *)
(*         \1 is canonical to 'FH 'F+ 'FU 'FO 'FP                             *)
(*         and can apply theory of this structure to \1 directly              *)
(******************************************************************************)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Reserved Notation "\Tr f" (at level 10, f at level 8).
Reserved Notation "P '^⟂'" (at level 8, format "P ^⟂").
Reserved Notation "f :⊗ g" (at level 45, left associativity).
Reserved Notation "'\Tr_' ( T ) f " (at level 10, f at level 8, format "'\Tr_' ( T )  f").
Reserved Notation "\Rank A" (at level 10, A at level 8, format "\Rank  A").

Reserved Notation "''FH'".
Reserved Notation "''F+'".
Reserved Notation "''FD'".
Reserved Notation "''FO'".
Reserved Notation "''FU'".
Reserved Notation "''FD1'".
Reserved Notation "''FP'".
Reserved Notation "''FP1'".
Reserved Notation "''FH[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''F+[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FD[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FO[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FU[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FD1[' H ]_ S" (at level 8, S at level 2).
Reserved Notation "''FP[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FP1[' H ]_ S" (at level 8, S at level 2).
Reserved Notation "''FH' ( V )"  (at level 8, format "''FH' ( V )").
Reserved Notation "''F+' ( V )"  (at level 8, format "''F+' ( V )").
Reserved Notation "''FD' ( V )"  (at level 8, format "''FD' ( V )").
Reserved Notation "''FO' ( V )"  (at level 8, format "''FO' ( V )").
Reserved Notation "''FU' ( V )" (at level 8, format "''FU' ( V )").
Reserved Notation "''FD1' ( V )" (at level 8, format "''FD1' ( V )").
Reserved Notation "''FP' ( V )" (at level 8, format "''FP' ( V )").
Reserved Notation "''FP1' ( V )"(at level 8, format "''FP1' ( V )").
Reserved Notation "[ 'herm' 'of' f 'as' g ]" (at level 0, format "[ 'herm'  'of'  f  'as'  g ]").
Reserved Notation "[ 'herm' 'of' f ]" (at level 0, format "[ 'herm'  'of'  f ]").
Reserved Notation "[ 'psd' 'of' f 'as' g ]" (at level 0, format "[ 'psd'  'of'  f  'as'  g ]").
Reserved Notation "[ 'psd' 'of' f ]" (at level 0, format "[ 'psd'  'of'  f ]").
Reserved Notation "[ 'den' 'of' f 'as' g ]" (at level 0, format "[ 'den'  'of'  f  'as'  g ]").
Reserved Notation "[ 'den' 'of' f ]" (at level 0, format "[ 'den'  'of'  f ]").
Reserved Notation "[ 'obs' 'of' f 'as' g ]" (at level 0, format "[ 'obs'  'of'  f  'as'  g ]").
Reserved Notation "[ 'obs' 'of' f ]" (at level 0, format "[ 'obs'  'of'  f ]").
Reserved Notation "[ 'unitary' 'of' f 'as' g ]" (at level 0, format "[ 'unitary'  'of'  f  'as'  g ]").
Reserved Notation "[ 'unitary' 'of' f ]" (at level 0, format "[ 'unitary'  'of'  f ]").
Reserved Notation "[ 'den1' 'of' f 'as' g ]" (at level 0, format "[ 'den1'  'of'  f  'as'  g ]").
Reserved Notation "[ 'den1' 'of' f ]" (at level 0, format "[ 'den1'  'of'  f ]").
Reserved Notation "[ 'proj' 'of' f 'as' g ]" (at level 0, format "[ 'proj'  'of'  f  'as'  g ]").
Reserved Notation "[ 'proj' 'of' f ]" (at level 0, format "[ 'proj'  'of'  f ]").
Reserved Notation "[ 'proj1' 'of' f 'as' g ]" (at level 0, format "[ 'proj1'  'of'  f  'as'  g ]").
Reserved Notation "[ 'proj1' 'of' f ]" (at level 0, format "[ 'proj1'  'of'  f ]").

Reserved Notation "''SO'" .
Reserved Notation "''SO_' S"     (at level 8, S at level 2, format "''SO_' S").
Reserved Notation "''SO_' ( S )" (at level 8).
Reserved Notation "''SO_' ( S , T )" (at level 8, format "''SO_' ( S ,  T )").
Reserved Notation "''SO[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''SO[' H ]_ ( S )"     (at level 8).
Reserved Notation "''SO[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''SO' ( S )"  (at level 8, format "''SO' ( S )").
Reserved Notation "''SO' ( S , T )"  (at level 8, format "''SO' ( S ,  T )").
(* Reserved Notation "[ 'SO' 'of' f 'as' g ]" (at level 0, format "[ 'SO'  'of'  f  'as'  g ]").
Reserved Notation "[ 'SO' 'of' f ]"  (at level 0, format "[ 'SO'  'of'  f ]"). *)

Reserved Notation ":1".
Reserved Notation "E ':o' F" (at level 50, F at next level).
Reserved Notation "E 'o:' F" (at level 50, F at next level).

Reserved Notation "\compl_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \compl_ i '/  '  F ']'").
Reserved Notation "\compl_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \compl_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\compl_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \compl_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\compl_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \compl_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\compl_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \compl_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\compl_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \compl_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\compl_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\compl_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\compl_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \compl_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\compl_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \compl_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\compl_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \compl_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\compl_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \compl_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\compr_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \compr_ i '/  '  F ']'").
Reserved Notation "\compr_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \compr_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\compr_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \compr_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\compr_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \compr_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\compr_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \compr_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\compr_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \compr_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\compr_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\compr_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\compr_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \compr_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\compr_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \compr_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\compr_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \compr_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\compr_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \compr_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "''PONB'".
Reserved Notation "''PONB' ( F ; S )"       (at level 8, format "''PONB' ( F ;  S )").
Reserved Notation "''PONB_' ( F ; S )"      (at level 8, format "''PONB_' ( F ;  S )").
Reserved Notation "''PONB[' H ]_ ( F ; S )"     (at level 8).
Reserved Notation "[ 'PONB' 'of' f 'as' g ]" (at level 0, format "[ 'PONB'  'of'  f  'as'  g ]").
Reserved Notation "[ 'PONB' 'of' f ]"  (at level 0, format "[ 'PONB'  'of'  f ]").

Reserved Notation "''ONB'".
Reserved Notation "''ONB' ( F ; S )"       (at level 8, format "''ONB' ( F ;  S )").
Reserved Notation "''ONB_' ( F ; S )"      (at level 8, format "''ONB_' ( F ;  S )").
Reserved Notation "''ONB[' H ]_ ( F ; S )"     (at level 8).
Reserved Notation "[ 'ONB' 'of' f 'as' g ]" (at level 0, format "[ 'ONB'  'of'  f  'as'  g ]").
Reserved Notation "[ 'ONB' 'of' f ]"  (at level 0, format "[ 'ONB'  'of'  f ]").

Reserved Notation "''NS'".
Reserved Notation "''NS_' S"       (at level 8, S at level 2, format "''NS_' S").
Reserved Notation "''NS_' ( S )"   (at level 8).
Reserved Notation "''NS[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''NS[' H ]_ ( S )"     (at level 8).
Reserved Notation "''NS' ( S )"    (at level 8, format "''NS' ( S )").
Reserved Notation "[ 'NS' 'of' f 'as' g ]" (at level 0, format "[ 'NS'  'of'  f  'as'  g ]").
Reserved Notation "[ 'NS' 'of' f ]"  (at level 0, format "[ 'NS'  'of'  f ]").

Reserved Notation "''TN'".
Reserved Notation "''TN_' ( F ; S )"      (at level 8, format "''TN_' ( F ;  S )").
Reserved Notation "''TN_' ( F ; S , T )"  (at level 8, format "''TN_' ( F ;  S ,  T )").
Reserved Notation "''TN[' H ]_ ( F ; S )"     (at level 8).
Reserved Notation "''TN[' H ]_ ( F ; S , T )" (at level 8).
Reserved Notation "''TN' ( F ; S )"       (at level 8, format "''TN' ( F ;  S )").
Reserved Notation "''TN' ( F ; S , T )"   (at level 8, format "''TN' ( F ;  S ,  T )").
Reserved Notation "[ 'TN' 'of' f 'as' g ]" (at level 0, format "[ 'TN'  'of'  f  'as'  g ]").
Reserved Notation "[ 'TN' 'of' f ]"  (at level 0, format "[ 'TN'  'of'  f ]").

Reserved Notation "''QM'".
Reserved Notation "''QM_' ( F ; S )"      (at level 8, format "''QM_' ( F ;  S )").
Reserved Notation "''QM_' ( F ; S , T )"  (at level 8, format "''QM_' ( F ;  S ,  T )").
Reserved Notation "''QM[' H ]_ ( F ; S )"     (at level 8).
Reserved Notation "''QM[' H ]_ ( F ; S , T )" (at level 8).
Reserved Notation "''QM' ( F ; S )"       (at level 8, format "''QM' ( F ;  S )").
Reserved Notation "''QM' ( F ; S , T )"   (at level 8, format "''QM' ( F ;  S ,  T )").
Reserved Notation "[ 'QM' 'of' f 'as' g ]" (at level 0, format "[ 'QM'  'of'  f  'as'  g ]").
Reserved Notation "[ 'QM' 'of' f ]"  (at level 0, format "[ 'QM'  'of'  f ]").

Reserved Notation "''CP'" .
Reserved Notation "''CP_' S"     (at level 8, S at level 2, format "''CP_' S").
Reserved Notation "''CP_' ( S )" (at level 8).
Reserved Notation "''CP_' ( S , T )" (at level 8, format "''CP_' ( S ,  T )").
Reserved Notation "''CP[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''CP[' H ]_ ( S )"     (at level 8).
Reserved Notation "''CP[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''CP' ( S )" (at level 8, format "''CP' ( S )").
Reserved Notation "''CP' ( S , T )"  (at level 8, format "''CP' ( S ,  T )").
Reserved Notation "[ 'CP' 'of' f 'as' g ]" (at level 0, format "[ 'CP'  'of'  f  'as'  g ]").
Reserved Notation "[ 'CP' 'of' f ]"  (at level 0, format "[ 'CP'  'of'  f ]").

Reserved Notation "''QO'" .
Reserved Notation "''QO_' S"     (at level 8, S at level 2, format "''QO_' S").
Reserved Notation "''QO_' ( S )" (at level 8).
Reserved Notation "''QO_' ( S , T )" (at level 8, format "''QO_' ( S ,  T )").
Reserved Notation "''QO[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''QO[' H ]_ ( S )"     (at level 8).
Reserved Notation "''QO[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''QO' ( S )" (at level 8, format "''QO' ( S )").
Reserved Notation "''QO' ( S , T )"  (at level 8, format "''QO' ( S ,  T )").
Reserved Notation "[ 'QO' 'of' f 'as' g ]" (at level 0, format "[ 'QO'  'of'  f  'as'  g ]").
Reserved Notation "[ 'QO' 'of' f ]"  (at level 0, format "[ 'QO'  'of'  f ]").

Reserved Notation "''QC'" .
Reserved Notation "''QC_' S"     (at level 8, S at level 2, format "''QC_' S").
Reserved Notation "''QC_' ( S )" (at level 8).
Reserved Notation "''QC_' ( S , T )" (at level 8, format "''QC_' ( S ,  T )").
Reserved Notation "''QC[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''QC[' H ]_ ( S )"     (at level 8).
Reserved Notation "''QC[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''QC' ( S )" (at level 8, format "''QC' ( S )").
Reserved Notation "''QC' ( S , T )"  (at level 8, format "''QC' ( S ,  T )").
Reserved Notation "[ 'QC' 'of' f 'as' g ]" (at level 0, format "[ 'QC'  'of'  f  'as'  g ]").
Reserved Notation "[ 'QC' 'of' f ]"  (at level 0, format "[ 'QC'  'of'  f ]").

Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.

Lemma eqb_iff (b1 b2 : bool): (b1 <-> b2) <-> b1 = b2.
Proof. by split=>[/Bool.eq_iff_eq_true|->]. Qed.
Lemma eq_iff (T : eqType) (t1 t2 : T) : t1 == t2 <-> t1 = t2.
Proof. by split=>[/eqP|->]. Qed.

Section lfunExtra.
Local Close Scope lfun_scope.

Lemma psdmx_tr (n : nat) (A : 'M[C]_n) :
  A^T \is psdmx = (A \is psdmx).
Proof.
suff P : forall (B : 'M[C]_n), B \is psdmx -> B^T \is psdmx.
case E: (A \is psdmx). by apply P. move: E. apply contraFF=>/P. by rewrite trmxK.
move=>B /psdmx_dot P. apply/psdmx_dot=>u. move: (P (map_mx conjC u)).
by rewrite -mxtrace_tr !trmx_mul !map_trmx trmxK map_mxCK mulmxA.
Qed.

Lemma obsmx_tr (n : nat) (A : 'M[C]_n) :
  A^T \is obsmx = (A \is obsmx).
Proof.
suff P : forall (B : 'M[C]_n), B \is obsmx -> B^T \is obsmx.
case E: (A \is obsmx). by apply P. move: E. apply contraFF=>/P. by rewrite trmxK.
move=>B /obsmx_dot P. apply/obsmx_dot=>u. move: (P (map_mx conjC u)).
by rewrite -mxtrace_tr -[\tr (u *m u ^*t)]mxtrace_tr !trmx_mul 
  -conjmxE !adjmxEl !trmxK conjmxK mulmxA.
Qed.

Lemma denmx_tr (n : nat) (A : 'M[C]_n) :
  A^T \is denmx = (A \is denmx).
Proof.
suff P : forall (B : 'M[C]_n), B \is denmx -> B^T \is denmx.
case E: (A \is denmx). by apply P. move: E. apply contraFF=>/P. by rewrite trmxK.
move=>B /denmxP[P1 P2]. apply/denmxP. by rewrite mxtrace_tr psdmx_tr P1 P2.
Qed.

Lemma psdmx_form (n : nat) (A : 'M[C]_n) :
  A \is psdmx -> exists B : 'M[C]_n , A = B *m B^*t.
Proof.
move=>/psdmxP[/hermmx_normal/unitarymx_spectralP P1 /nnegmxP P2].
exists ((spectralmx A) ^*t *m diag_mx (sqrtdmx (spectral_diag A))).
rewrite adjmxM adjmxK {1}P1 !mulmxA. f_equal.
rewrite -!mulmxA. f_equal. rewrite diag_mx_adj diag_mx_dmul. f_equal.
apply/matrixP=>i j; rewrite !mxE -normCK real_normK ?sqrtCK// realE sqrtC_ge0.
apply/orP; left; by apply P2.
Qed.

Lemma conjmx_trC (n m: nat) (A : 'M[C]_(n,m)) : A^*m^T = A^T^*m.
Proof. by apply/matrixP=>i j; rewrite !mxE. Qed.

Lemma conjmx_map (n m: nat) (A : 'M[C]_(n,m)) : map_mx conjC A = A^*m.
Proof. by apply/matrixP=>i j; rewrite !mxE. Qed.

Definition lftrace (H: chsType) (f: 'End(H)) :=
  \tr (f2mx f).

Local Notation "\Tr f" := (@lftrace _ f).

Lemma lftrace_baseE (H: chsType) (f: 'End(H)) :
  \Tr f = \sum_i [< eb i ; f (eb i) >].
Proof. 
rewrite /lftrace /mxtrace; apply eq_bigr=>i _; rewrite dotp_mulmx unlock/= /eb !r2vK 
  mxE (bigD1 i)//= !mxE !eqxx conjC1 mul1r (bigD1 i)//= mxE !eqxx mul1r !big1 ?addr0//.
all: by move=>j /negPf nji; rewrite !mxE nji andbF ?conjC0 mul0r.
Qed.

Lemma mxtraceE {R: ringType} n (A : 'M[R]_n) :
  \tr A = \sum_i A i i.
Proof. by []. Qed.

Lemma lftraceC (H G : chsType) (f: 'Hom(H,G)) (g: 'Hom(G,H)) :
  \Tr (f \o g) = \Tr (g \o f).
Proof.
rewrite /lftrace /comp_lfun unlock/= /lin1_mx/= /mxtrace.
have P: forall n (A: 'M[C]_n) i, (delta_mx 0 i *m A) 0 i = A i i.
move=>n m A i. rewrite !mxE (bigD1 i)//= !mxE !eqxx mul1r big1 ?addr0//.
by move=>j /negPf nji; rewrite mxE nji andbF mul0r.
under eq_bigr do rewrite !mxE unlock/= !r2vK -mulmxA P.
rewrite -[LHS]mxtraceE mxtrace_mulC mxtraceE. apply eq_bigr=>i _.
by rewrite [RHS]mxE unlock/= !r2vK -mulmxA P.
Qed.

Lemma lftrace_is_linear (H: chsType) : linear_for *%R (@lftrace H).
Proof. move=>c f g; by rewrite /lftrace !linearP/=. Qed.
Canonical lftrace_additive (H: chsType) := Additive (@lftrace_is_linear H).
Canonical lftrace_linear (H: chsType) := Linear (@lftrace_is_linear H).

Lemma lftrace_adj (H: chsType) (f: 'End(H)) : \Tr f^A = (\Tr f)^*.
Proof. by rewrite /lftrace !mxtraceE raddf_sum; under eq_bigr do rewrite !mxE. Qed.

Lemma lftrace_tr (H: chsType) (f: 'End(H)) : \Tr f^T = (\Tr f).
Proof. by rewrite /lftrace !mxtraceE; under eq_bigr do rewrite !mxE. Qed.

Lemma lftrace_conj (H: chsType) (f: 'End(H)) : \Tr f^C = (\Tr f)^*.
Proof. by rewrite conjfAT lftrace_tr lftrace_adj. Qed.

Lemma dotp_ebl (H: chsType) (u: H) i : [< eb i; u >] = ((v2r u) 0 i).
Proof.
rewrite (decv u) !linear_sum summxE/=; apply eq_bigr=>j _.
by rewrite !linearZ/= cbase mxE /eb r2vK mxE eqxx/=.
Qed.

Lemma dotp_ebr (H: chsType) (u: H) i : [< u; eb i >] = ((v2r u) 0 i)^*.
Proof. by rewrite -conj_dotp dotp_ebl. Qed.

Lemma outp_trlf (H : chsType) (u v : H) : \Tr [> u; v <] = [< v; u >].
Proof.
rewrite lftrace_baseE. under eq_bigr do rewrite outpE linearZ/=; symmetry.
rewrite {1}(decv u) {1}(decv v) linear_suml/=; apply eq_bigr=>i _.
by rewrite linearZl/= linear_sumr/= (bigD1 i)//= big1=>[j/negPf nj|];
rewrite linearZ/= cbase ?eqxx 1?eq_sym ?nj ?mulr0// mulr1 addr0 dotp_ebl dotp_ebr.
Qed.
  
Lemma intro_eb (H G: chsType) (f g: 'Hom(H,G)) : 
  (forall i, f (eb i) = g (eb i)) <-> f = g.
Proof.
split=>[P|->//]; apply/lfunP=>u; rewrite (decv u) !linear_sum/=.
by apply eq_bigr=>i _; rewrite !linearZ/= P.
Qed.

(* Definition delta_lf (H G: chsType) i j : 'Hom(H,G) := Vector.Hom (delta_mx j i).
Check delta_lf. *)

Lemma eb_out (H G: chsType) i j : 
  [> eb i ; eb j <] = Vector.Hom (delta_mx j i) :> 'Hom(H,G).
Proof. 
by apply/intro_eb=>k; rewrite outpE cbase unlock/= /eb r2vK 
  mul_delta_mx_cond -[in RHS]scaler_nat linearZ eq_sym.
Qed.

Lemma sumeb_out (H: chsType) : \sum_i [> eb i; eb i <] = \1%VF :> 'End(H).
Proof.
under eq_bigr do rewrite eb_out.
by rewrite -linear_sum/= -mx1_sum_delta; apply/f2mx_inj; rewrite f2mx1/=.
Qed.

Definition delta_lf (H G: chsType) i j : 'Hom(H,G) := [> eb i; eb j <].

Lemma delta_lfE (H G: chsType) i j :
  (delta_lf i j : 'Hom(H,G)) = Vector.Hom (delta_mx j i).
Proof. exact: eb_out. Qed.

Lemma delta_lf_eb (H G: chsType) i j k :
  (delta_lf i j : 'Hom(H,G)) (eb k) = (k == j)%:R *: eb i.
Proof. by rewrite /delta_lf outpE cbase eq_sym. Qed.

Lemma comp_delta_lf_cond (H G W: chsType) i j k l :
  ((delta_lf i j : 'Hom(G,W)) \o (delta_lf k l : 'Hom(H,G)) = (j == k)%:R *: delta_lf i l)%VF.
Proof. by rewrite /delta_lf outp_comp cbase. Qed.

Lemma comp_delta_lf (H G W: chsType) i j k :
  ((delta_lf i j : 'Hom(G,W)) \o (delta_lf j k : 'Hom(H,G)) = delta_lf i k)%VF.
Proof. by rewrite comp_delta_lf_cond eqxx scale1r. Qed.

Lemma trlf_deltar (H G: chsType) (f: 'Hom(H,G)) i j :
  \Tr (f \o delta_lf i j) = [< eb j; f (eb i) >].
Proof.
rewrite lftrace_baseE (bigD1 j)// big1/=.
by move=>k /negPf nkj; rewrite lfunE/= delta_lf_eb nkj scale0r !linear0.
by rewrite lfunE/= delta_lf_eb eqxx scale1r addr0.
Qed.

Lemma trlf_intror (H G: chsType) (f1 f2: 'Hom(H,G)) :
  reflect (forall g, \Tr (f1 \o g) = \Tr (f2 \o g)) (f1 == f2).
Proof.
apply/(iffP eqP)=>[->//|P]; apply/intro_eb=>/=i. apply/intro_ebl=>/= j.
by rewrite -!trlf_deltar P.
Qed.

Lemma trlf_introl (H G: chsType) (f1 f2: 'Hom(H,G)) :
  reflect (forall g, \Tr (g \o f1) = \Tr (g \o f2)) (f1 == f2).
Proof.
apply/(iffP eqP)=>[->//|P].
apply/intro_eb=>/=i. apply/intro_ebl=>/= j.
by rewrite -!trlf_deltar lftraceC P lftraceC.
Qed.

Lemma lfun_sum_delta (H G: chsType) (f: 'Hom(H,G)) :
  f = \sum_j\sum_i [< eb i; f (eb j) >] *: delta_lf i j.
Proof.
apply/intro_eb=>i. apply/intro_ebl=>/= j.
rewrite sum_lfunE (bigD1 i)// big1/=.
move=>k /negPf nkj. all: rewrite sum_lfunE; under eq_bigr do 
  rewrite lfunE/= delta_lf_eb 1 ?eq_sym ?nkj ?eqxx ?scale0r ?scale1r ?scaler0.
rewrite big1//. rewrite addr0 linear_sum/= (bigD1 j)// big1/=.
by move=>k /negPf nkj; rewrite linearZ/= cbase eq_sym nkj mulr0.
by rewrite linearZ/= cbase eqxx addr0 mulr1.
Qed.

Lemma nneg_form (R: numClosedFieldType) m (U : 'M[R]_m) (D:'rV_m) :
  D \is a nnegmx -> U^*t *m diag_mx D *m U \is psdmx.
Proof.
move/nnegmxP=> P1; apply/psdmx_dot=>u.
have: \tr ((u *m U^*t) *m diag_mx D *m (u *m U^*t)^*t) \is Num.nneg.
rewrite mx_dot_diag_mx nnegrE sumr_ge0// =>i _.
by rewrite mulr_ge0 ?exprn_ge0// -nnegrE P1.
by rewrite adjmxM adjmxK !mulmxA.
Qed.

Lemma hermmx_psd_decomp (R: numClosedFieldType) m (M : 'M[R]_m) :
  M \is hermmx -> exists (M1 M2 : 'M[R]_m), M1 \is psdmx /\
  M2 \is psdmx /\ M1 - M2 = M.
Proof.
move=>Ph. move: {+}Ph=>/hermmx_normal/unitarymx_spectralP P0.
move: {+}Ph=>/hermitian_spectral_diag_real P1.
set D1 := \matrix_(i,j) if (spectral_diag M i j) >= 0 then 
  (spectral_diag M i j) else 0.
set D2 := \matrix_(i,j) if ~~((spectral_diag M i j) >= 0) then 
  - (spectral_diag M i j) else 0.
have P2: D1 - D2 = spectral_diag M.
apply/matrixP=>i j. rewrite !mxE. case: (0 <= spectral_diag M i j)=>/=.
by rewrite subr0. by rewrite opprK add0r.
have P3: D1 \is a nnegmx. apply/nnegmxP=>i j. 
rewrite mxE. case E: (0 <= spectral_diag M i j)=>//=. by rewrite nnegrE.
have P4: D2 \is a nnegmx. apply/nnegmxP=>i j. 
rewrite mxE. case E: (0 <= spectral_diag M i j)=>/=. by rewrite nnegrE.
rewrite nnegrE oppr_ge0. move: P1=>/realmxP/(_ i j). by rewrite realE E.
exists ((spectralmx M) ^*t *m diag_mx D1 *m spectralmx M).
exists ((spectralmx M) ^*t *m diag_mx D2 *m spectralmx M).
do ?split. 1,2: by apply/nneg_form.
by rewrite [RHS]P0 -P2 linearB/= linearBr/= linearBl/=.
Qed.

Lemma reim_decomp (R: numClosedFieldType) (a b : R) :
  a = (a + b^*)/2%:R + 'i * (- 'i * (a - b^*)/2%:R) /\ 
  b = ((a + b^*)/2%:R)^* + 'i * (- 'i * (a - b^*)/2%:R)^*.
Proof.
rewrite -{3}(conjCK 'i) -rmorphM -rmorphD conjCi !mulrA mulrN -!expr2 sqrrN.
by rewrite  !sqrCi opprK !mulNr !mul1r -mulrDl -mulrBl opprB [a-_]addrC 
  [_+(b^*- _)]addrC !addrA addrK addrNK -!mulr2n -mulr_natr mulfK ?pnatr_eq0//
  -mulr_natr mulfK ?pnatr_eq0// conjCK.
Qed.

Lemma mx_herm_decomp (R: numClosedFieldType) m (M : 'M[R]_m) : 
  exists (M1 M2 : 'M[R]_m), M1 \is hermmx /\ M2 \is hermmx /\ M1 + 'i *: M2 = M.
Proof.
set M1 := \matrix_(i,j) ((M i j + (M j i)^*)/2%:R).
set M2 := \matrix_(i,j) ((- 'i * (M i j - (M j i)^*)/2%:R)).
exists M1. exists M2.
do ? split. 1,2: apply/hermmxP/matrixP=>i j; rewrite /M1 /M2 !mxE 
  !rmorphM -?conjCi ?conjCK ?conjCi 1 ?mulNr -?mulrN ?rmorphB ?rmorphD conjCK ?opprB;
  congr (_ * _). by rewrite addrC. 
1,2: by symmetry; apply/conj_Creal; rewrite realV realn.
apply/matrixP=>i j. rewrite !mxE. by move: (reim_decomp (M i j) (M j i))=>[ <-].
Qed.

Lemma mx_psd_decomp (R: numClosedFieldType) m (M : 'M[R]_m) :
  exists (M1 M2 M3 M4 : 'M[R]_m) , M1 \is psdmx /\ M2 \is psdmx 
  /\ M3 \is psdmx /\ M4 \is psdmx /\ M = M1 - M2 + 'i *: M3 - 'i *: M4.
Proof.
move: (mx_herm_decomp M)=>[N1 [N2 [/hermmx_psd_decomp [M1 [M2 [P1 [P2 P3]]]] 
  [/hermmx_psd_decomp [M3 [M4 [P4 [P5 P6]]]] P7]]]].
exists M1. exists M2. exists M3. exists M4.
do ? split=>//. by rewrite -P7 -P3 -P6 scalerBr addrA.
Qed.

Lemma trmxC_delta (R: numClosedFieldType) m n i j :
  (delta_mx i j : 'M[R]_(m,n))^*t = delta_mx j i.
Proof. by apply/matrixP=>x y; rewrite !mxE andbC conjC_nat. Qed.

Lemma mulmxACA (R: ringType) m1 m2 m3 m4 m5 
 (M1 :'M[R]_(m1,m2)) (M2 : 'M_(m2,m3)) (M3 : 'M_(m3,m4)) (M4 : 'M_(m4,m5)) :
  M1 *m M2 *m M3 *m M4 = M1 *m (M2 *m M3) *m M4.
Proof. by rewrite !mulmxA. Qed.

Lemma delta_mx_mulEl (R: comRingType) {m n l} (A : 'M[R]_(m , n)) i (j:'I_l) p q :
  (A *m delta_mx i j) p q = (j == q)%:R * A p i.
Proof.
rewrite mxE (bigD1 i)// big1/= ?mxE ?eqxx/= ?addr0 1?eq_sym 1?mulrC//.
move=>k /negPf Pk; rewrite mxE Pk/= mulr0//.
Qed.

Lemma delta_mx_mulEr (R: comRingType) {m n l} (A : 'M[R]_(m , n)) (i:'I_l) j p q :
  (delta_mx i j *m A) p q = (i == p)%:R * A j q.
Proof.
rewrite mxE (bigD1 j)// big1/= ?mxE ?eqxx/= ?addr0 1?eq_sym ?andbT//.
move=>k /negPf Pk; rewrite mxE Pk/= andbF mul0r//.
Qed.

Lemma adjmx1 (R: numClosedFieldType) m : (1%:M : 'M[R]_m)^*t = 1%:M.
Proof. apply/matrixP=>i j. by rewrite !mxE eq_sym conjC_nat. Qed.

Lemma psdmxZ (T: numClosedFieldType) m (A: 'M[T]_m) c :
  0 <= c -> A \is psdmx -> c *: A \is psdmx.
Proof.
move=>Pc /psdmx_dot PA. apply/psdmx_dot=>u.
by rewrite nnegrE -scalemxAr -scalemxAl linearZ/= mulr_ge0// -nnegrE PA.
Qed.

Lemma diag_decomp_absorb m (A: 'M[C]_m) : A \is psdmx -> 
  let v k := (sqrtC (spectral_diag A 0 k) *: row k (spectralmx A)) in 
A = \sum_k (v k)^*t *m (v k).
Proof.
move=>P/=; have P1 i: `|sqrtC (spectral_diag A 0 i)| = sqrtC (spectral_diag A 0 i).
by rewrite ger0_norm// sqrtC_ge0 -nnegrE; move: P=>/psdmxP[_ /nnegmxP/(_ 0 i)].
under eq_bigr do rewrite adjmxZ adjmxE tr_row map_col -scalemxAl scalemxAr scalerA 
  -normCKC P1 sqrtCK -row_diag_mul; rewrite -mulmx_colrow mulmxA.
by move:P=>/psdmxP[/hermmx_normal/unitarymx_spectralP].
Qed.

Lemma le_lownerE_psdtr m (A B: 'M[C]_m) : 
  reflect (forall x, x \is psdmx -> \tr (A *m x) <= \tr (B *m x)) (A ⊑ B).
Proof.
rewrite le_lownerE. 
apply/(iffP (@psdmx_dot _ _ _))=>[P x /diag_decomp_absorb ->|P x].
rewrite !mulmx_sumr !linear_sum/= ler_sum // => i _.
by rewrite -subr_ge0 -linearB -mulmxBl/= mulmxA mxtrace_mulC -nnegrE mulmxA P.
rewrite -mulmxA mxtrace_mulC -mulmxA nnegrE mulmxBl linearB/= subr_ge0.
apply P. apply formV_psd.
Qed.

Lemma le_lownerE_dentr m (A B: 'M[C]_m) : 
  reflect (forall x, x \is denmx -> \tr (A *m x) <= \tr (B *m x)) (A ⊑ B).
Proof.
apply/(iffP (@le_lownerE_psdtr _ _ _))=>H x Px.
apply H. by apply/denmx_psd.
case E: (x == 0). move/eqP: E=>->. by rewrite !linear0.
have P: \tr| x| != 0 by rewrite trnorm_eq0 E.
have : (\tr| x |)^-1 *: x \is denmx. apply/denmxP. split. 
apply psdmxZ=>//. by rewrite invr_ge0 trnorm_ge0.
by rewrite linearZ/= -(psdmx_trnorm Px)  mulVf.
move=>/H. rewrite -!scalemxAr !linearZ/= mulrC [_^-1*_]mulrC ler_pdivr_mulr.
by rewrite lt_def P trnorm_ge0. rewrite mulrVK//.
Qed.

End lfunExtra.

Notation "\Tr f" := (@lftrace _ f).

Section Lfpred.
Context {R : numClosedFieldType} (V: vectType R).

Definition hermlf :=
  [qualify A : 'End(V) | f2mx A \is hermmx].
Fact hermlf_key : pred_key hermlf. Proof. by []. Qed.
Canonical hermlf_keyed := KeyedQualifier hermlf_key.

Definition psdlf :=
  [qualify A : 'End(V) | f2mx A \is psdmx].
Fact psdlf_key : pred_key psdlf. Proof. by []. Qed.
Canonical psdlf_keyed := KeyedQualifier psdlf_key.

Definition denlf :=
  [qualify A : 'End(V) | f2mx A \is denmx].
Fact denlf_key : pred_key denlf. Proof. by []. Qed.
Canonical denlf_keyed := KeyedQualifier denlf_key.

Definition obslf :=
  [qualify A : 'End(V) | f2mx A \is obsmx].
Fact obslf_key : pred_key obslf. Proof. by []. Qed.
Canonical obslf_keyed := KeyedQualifier obslf_key.

Definition unitarylf :=
  [qualify A : 'End(V) | f2mx A \is unitarymx].
Fact unitarylf_key : pred_key unitarylf. Proof. by []. Qed.
Canonical unitarylf_keyed := KeyedQualifier unitarylf_key.

Definition den1lf :=
  [qualify A : 'End(V) | f2mx A \is den1mx].
Fact den1lf_key : pred_key den1lf. Proof. by []. Qed.
Canonical den1lf_keyed := KeyedQualifier den1lf_key.

Definition projlf :=
  [qualify A : 'End(V) | f2mx A \is projmx].
Fact projlf_key : pred_key projlf. Proof. by []. Qed.
Canonical projlf_keyed := KeyedQualifier projlf_key.

Definition proj1lf :=
  [qualify A : 'End(V) | f2mx A \is proj1mx].
Fact proj1lf_key : pred_key proj1lf. Proof. by []. Qed.
Canonical proj1lf_keyed := KeyedQualifier proj1lf_key.

Lemma psdlf_herm A : A \is psdlf -> A \is hermlf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/psdmx_herm. Qed.

Lemma denlf_psd A : A \is denlf -> A \is psdlf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/denmx_psd. Qed.
Lemma denlf_obs A : A \is denlf -> A \is obslf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/denmx_obs. Qed.
Lemma denlf_herm A : A \is denlf -> A \is hermlf.
Proof. by move=>/denlf_psd/psdlf_herm. Qed.

Lemma obslf_psd A : A \is obslf -> A \is psdlf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/obsmx_psd. Qed.
Lemma obslf_herm A : A \is obslf -> A \is hermlf.
Proof. by move=>/obslf_psd/psdlf_herm. Qed.

Lemma den1lf_den A : A \is den1lf -> A \is denlf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/den1mx_den. Qed.
Lemma den1lf_psd A : A \is den1lf -> A \is psdlf.
Proof. by move=>/den1lf_den/denlf_psd. Qed.
Lemma den1lf_obs A : A \is den1lf -> A \is obslf.
Proof. by move=>/den1lf_den/denlf_obs. Qed.
Lemma den1lf_herm A : A \is den1lf -> A \is hermlf.
Proof. by move=>/den1lf_den/denlf_herm. Qed.

Lemma projlf_obs A : A \is projlf -> A \is obslf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/projmx_obs. Qed.
Lemma projlf_psd A : A \is projlf -> A \is psdlf.
Proof. by move=>/projlf_obs/obslf_psd. Qed.
Lemma projlf_herm A : A \is projlf -> A \is hermlf.
Proof. by move=>/projlf_obs/obslf_herm. Qed.

Lemma proj1lf_den1 A : A \is proj1lf -> A \is den1lf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/proj1mx_den1. Qed.
Lemma proj1lf_proj A : A \is proj1lf ->  A \is projlf.
Proof. by rewrite qualifE [in X in _->X]qualifE=>/proj1mx_proj. Qed.
Lemma proj1lf_den A : A \is proj1lf -> A \is denlf.
Proof. by move=>/proj1lf_den1/den1lf_den. Qed.
Lemma proj1lf_psd A : A \is proj1lf -> A \is psdlf.
Proof. by move=>/proj1lf_den/denlf_psd. Qed.
Lemma proj1lf_obs A : A \is proj1lf -> A \is obslf.
Proof. by move=>/proj1lf_den/denlf_obs. Qed.
Lemma proj1lf_herm A : A \is proj1lf -> A \is hermlf.
Proof. by move=>/proj1lf_den/denlf_herm. Qed.

End Lfpred.

Arguments hermlf {R V}.
Arguments psdlf {R V}.
Arguments denlf {R V}.
Arguments obslf {R V}.
Arguments unitarylf {R V}.
Arguments den1lf {R V}.
Arguments projlf {R V}.
Arguments proj1lf {R V}.

(*---------------------------------------------------------------*)
(* psdlf  :  variant  (maybe sigma type?)                        *)
(* hierachy : psdlf -> obslf -> denlf                            *)
(*---------------------------------------------------------------*)
(* currently they are all sigma type from 'End(V) directly       *)
(* TODO: Improve them by: define sigma type of psdlf as basis    *)
(* Then define the type hierachy : psdlf -> obslf -> denlf       *)
(*---------------------------------------------------------------*)
(* change: using structure instead of sigma type;                *)
(* using canonical to ensure that lfun is unitary                *)
(*---------------------------------------------------------------*)
Module LfunPred.

(* not sure if we need phV below *)
Section ClassDef.
Variable (V: chsType).
Implicit Type (phV : phant V).

Notation axiom_herm f := (f \is hermlf).
Notation axiom_psd f := (f \is psdlf).
Notation axiom_den f := (f \is denlf).
Notation axiom_obs f := (f \is obslf).
Notation axiom_unitary f := (f \is unitarylf).
Notation axiom_den1 f := (f \is den1lf).
Notation axiom_proj f := (f \is projlf).
Notation axiom_proj1 f := (f \is proj1lf).

Structure type_herm (phV : phant V) := Pack_herm { sort_herm: 'End(V); _ : axiom_herm sort_herm; }.
Structure type_psd (phV : phant V) := Pack_psd { sort_psd: 'End(V); _ : axiom_psd sort_psd; }.
Structure type_den (phV : phant V) := Pack_den { sort_den: 'End(V); _ : axiom_den sort_den; }.
Structure type_obs (phV : phant V) := Pack_obs { sort_obs: 'End(V); _ : axiom_obs sort_obs; }.
Structure type_unitary (phV : phant V) := Pack_unitary { sort_unitary: 'End(V); _ : axiom_unitary sort_unitary; }.
Structure type_den1 (phV : phant V) := Pack_den1 { sort_den1: 'End(V); _ : axiom_den1 sort_den1; }.
Structure type_proj (phV : phant V) := Pack_proj { sort_proj: 'End(V); _ : axiom_proj sort_proj; }.
Structure type_proj1 (phV : phant V) := Pack_proj1 { sort_proj1: 'End(V); _ : axiom_proj1 sort_proj1; }.

Local Coercion sort_herm : type_herm >-> Vector.hom.
Local Coercion sort_psd : type_psd >-> Vector.hom.
Local Coercion sort_den : type_den >-> Vector.hom.
Local Coercion sort_obs : type_obs >-> Vector.hom.
Local Coercion sort_unitary : type_unitary >-> Vector.hom.
Local Coercion sort_den1 : type_den1 >-> Vector.hom.
Local Coercion sort_proj : type_proj >-> Vector.hom.
Local Coercion sort_proj1 : type_proj1 >-> Vector.hom.

Variables (phV : phant V) (T : 'End(V)) (cT_herm : type_herm phV) (cT_psd : type_psd phV).
Variables (cT_den : type_den phV) (cT_obs : type_obs phV) (cT_unitary : type_unitary phV).
Variables (cT_den1 : type_den1 phV) (cT_proj : type_proj phV) (cT_proj1 : type_proj1 phV).
Definition class_herm := let: Pack_herm _ c as cT' := cT_herm return (axiom_herm (cT' : 'End(V))) in c.
Definition clone_herm c of phant_id class_herm c := @Pack_herm phV T c.
Definition class_psd := let: Pack_psd _ c as cT' := cT_psd return (axiom_psd (cT' : 'End(V))) in c.
Definition clone_psd c of phant_id class_psd c := @Pack_psd phV T c.
Definition class_den := let: Pack_den _ c as cT' := cT_den return (axiom_den (cT' : 'End(V))) in c.
Definition clone_den c of phant_id class_den c := @Pack_den phV T c.
Definition class_obs := let: Pack_obs _ c as cT' := cT_obs return (axiom_obs (cT' : 'End(V))) in c.
Definition clone_obs c of phant_id class_obs c := @Pack_obs phV T c.
Definition class_unitary := let: Pack_unitary _ c as cT' := cT_unitary return (axiom_unitary (cT' : 'End(V))) in c.
Definition clone_unitary c of phant_id class_unitary c := @Pack_unitary phV T c.
Definition class_den1 := let: Pack_den1 _ c as cT' := cT_den1 return (axiom_den1 (cT' : 'End(V))) in c.
Definition clone_den1 c of phant_id class_den1 c := @Pack_den1 phV T c.
Definition class_proj := let: Pack_proj _ c as cT' := cT_proj return (axiom_proj (cT' : 'End(V))) in c.
Definition clone_proj c of phant_id class_proj c := @Pack_proj phV T c.
Definition class_proj1 := let: Pack_proj1 _ c as cT' := cT_proj1 return (axiom_proj1 (cT' : 'End(V))) in c.
Definition clone_proj1 c of phant_id class_proj1 c := @Pack_proj1 phV T c.

Fact hermf_key : unit. Proof. by []. Qed.
Fact psdf_key : unit. Proof. by []. Qed.
Fact denf_key : unit. Proof. by []. Qed.
Fact obsf_key : unit. Proof. by []. Qed.
Fact unitaryf_key : unit. Proof. by []. Qed.
Fact den1f_key : unit. Proof. by []. Qed.
Fact projf_key : unit. Proof. by []. Qed.
Fact proj1f_key : unit. Proof. by []. Qed.
Definition hermf_of_lfun_def f (DO : f \is hermlf) := (@Pack_herm (Phant V) _ DO).
Definition psdf_of_lfun_def f (DO : f \is psdlf) := (@Pack_psd (Phant V) _ DO).
Definition denf_of_lfun_def f (DO : f \is denlf) := (@Pack_den (Phant V) _ DO).
Definition obsf_of_lfun_def f (DO : f \is obslf) := (@Pack_obs (Phant V) _ DO).
Definition unitaryf_of_lfun_def f (DO : f \is unitarylf) := (@Pack_unitary (Phant V) _ DO).
Definition den1f_of_lfun_def f (DO : f \is den1lf) := (@Pack_den1 (Phant V) _ DO).
Definition projf_of_lfun_def f (DO : f \is projlf) := (@Pack_proj (Phant V) _ DO).
Definition proj1f_of_lfun_def f (DO : f \is proj1lf) := (@Pack_proj1 (Phant V) _ DO).
Definition hermf_of_lfun k := locked_with k (@hermf_of_lfun_def).
Definition psdf_of_lfun k := locked_with k (@psdf_of_lfun_def).
Definition denf_of_lfun k := locked_with k (@denf_of_lfun_def).
Definition obsf_of_lfun k := locked_with k (@obsf_of_lfun_def).
Definition unitaryf_of_lfun k := locked_with k (@unitaryf_of_lfun_def).
Definition den1f_of_lfun k := locked_with k (@den1f_of_lfun_def).
Definition projf_of_lfun k := locked_with k (@projf_of_lfun_def).
Definition proj1f_of_lfun k := locked_with k (@proj1f_of_lfun_def).
Local Canonical hermf_unlockable k := [unlockable fun hermf_of_lfun k].
Local Canonical psdf_unlockable k := [unlockable fun psdf_of_lfun k].
Local Canonical denf_unlockable k := [unlockable fun denf_of_lfun k].
Local Canonical obsf_unlockable k := [unlockable fun obsf_of_lfun k].
Local Canonical unitaryf_unlockable k := [unlockable fun unitaryf_of_lfun k].
Local Canonical den1f_unlockable k := [unlockable fun den1f_of_lfun k].
Local Canonical projf_unlockable k := [unlockable fun projf_of_lfun k].
Local Canonical proj1f_unlockable k := [unlockable fun proj1f_of_lfun k].

Lemma hermfE k f (DO : f \is hermlf) : (hermf_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.
Lemma psdfE k f (DO : f \is psdlf) : (psdf_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.
Lemma denfE k f (DO : f \is denlf) : (denf_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.
Lemma obsfE k f (DO : f \is obslf) : (obsf_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.
Lemma unitaryfE k f (DO : f \is unitarylf) : (unitaryf_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.
Lemma den1fE k f (DO : f \is den1lf) : (den1f_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.
Lemma projfE k f (DO : f \is projlf) : (projf_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.
Lemma proj1fE k f (DO : f \is proj1lf) : (proj1f_of_lfun k DO) = f :> 'End(V).
Proof. by rewrite unlock. Qed.

End ClassDef.

Section Algebraic.
Variable (V: chsType) (phV : phant V).

Local Canonical herm_subType    := Eval hnf in [subType for (@sort_herm _ phV)].
Definition herm_eqMixin         := Eval hnf in [eqMixin of (type_herm phV) by <:].
Local Canonical herm_eqType     := Eval hnf in EqType (type_herm phV) herm_eqMixin.
Definition herm_choiceMixin     := Eval hnf in [choiceMixin of (type_herm phV) by <:].
Local Canonical herm_choiceType := Eval hnf in ChoiceType (type_herm phV) herm_choiceMixin.
Local Canonical psd_subType    := Eval hnf in [subType for (@sort_psd _ phV)].
Definition psd_eqMixin         := Eval hnf in [eqMixin of (type_psd phV) by <:].
Local Canonical psd_eqType     := Eval hnf in EqType (type_psd phV) psd_eqMixin.
Definition psd_choiceMixin     := Eval hnf in [choiceMixin of (type_psd phV) by <:].
Local Canonical psd_choiceType := Eval hnf in ChoiceType (type_psd phV) psd_choiceMixin.
Local Canonical den_subType    := Eval hnf in [subType for (@sort_den _ phV)].
Definition den_eqMixin         := Eval hnf in [eqMixin of (type_den phV) by <:].
Local Canonical  den_eqType    := Eval hnf in EqType (type_den phV) den_eqMixin.
Definition den_choiceMixin     := Eval hnf in [choiceMixin of (type_den phV) by <:].
Local Canonical den_choiceType := Eval hnf in ChoiceType (type_den phV) den_choiceMixin.
Local Canonical obs_subType    := Eval hnf in [subType for (@sort_obs _ phV)].
Definition obs_eqMixin         := Eval hnf in [eqMixin of (type_obs phV) by <:].
Local Canonical obs_eqType     := Eval hnf in EqType (type_obs phV) obs_eqMixin.
Definition obs_choiceMixin     := Eval hnf in [choiceMixin of (type_obs phV) by <:].
Local Canonical obs_choiceType := Eval hnf in ChoiceType (type_obs phV) obs_choiceMixin.
Local Canonical unitary_subType:= Eval hnf in [subType for (@sort_unitary _ phV)].
Definition unitary_eqMixin     := Eval hnf in [eqMixin of (type_unitary phV) by <:].
Local Canonical unitary_eqType := Eval hnf in EqType (type_unitary phV) unitary_eqMixin.
Definition unitary_choiceMixin := Eval hnf in [choiceMixin of (type_unitary phV) by <:].
Local Canonical unitary_choiceType := Eval hnf in ChoiceType (type_unitary phV) unitary_choiceMixin.
Local Canonical den1_subType   := Eval hnf in [subType for (@sort_den1 _ phV)].
Definition den1_eqMixin        := Eval hnf in [eqMixin of (type_den1 phV) by <:].
Local Canonical den1_eqType    := Eval hnf in EqType (type_den1 phV) den1_eqMixin.
Definition den1_choiceMixin    := Eval hnf in [choiceMixin of (type_den1 phV) by <:].
Local Canonical den1_choiceType:= Eval hnf in ChoiceType (type_den1 phV) den1_choiceMixin.
Local Canonical proj_subType   := Eval hnf in [subType for (@sort_proj _ phV)].
Definition proj_eqMixin        := Eval hnf in [eqMixin of (type_proj phV) by <:].
Local Canonical proj_eqType    := Eval hnf in EqType (type_proj phV) proj_eqMixin.
Definition proj_choiceMixin    := Eval hnf in [choiceMixin of (type_proj phV) by <:].
Local Canonical proj_choiceType:= Eval hnf in ChoiceType (type_proj phV) proj_choiceMixin.
Local Canonical proj1_subType  := Eval hnf in [subType for (@sort_proj1 _ phV)].
Definition proj1_eqMixin       := Eval hnf in [eqMixin of (type_proj1 phV) by <:].
Local Canonical proj1_eqType   := Eval hnf in EqType (type_proj1 phV) proj1_eqMixin.
Definition proj1_choiceMixin   := Eval hnf in [choiceMixin of (type_proj1 phV) by <:].
Local Canonical proj1_choiceType:= Eval hnf in ChoiceType (type_proj1 phV) proj1_choiceMixin.

End Algebraic.

Module Import Exports.
Coercion sort_herm : type_herm >-> Vector.hom.
Coercion sort_psd : type_psd >-> Vector.hom.
Coercion sort_den : type_den >-> Vector.hom.
Coercion sort_obs : type_obs >-> Vector.hom.
Coercion sort_unitary : type_unitary >-> Vector.hom.
Coercion sort_den1 : type_den1 >-> Vector.hom.
Coercion sort_proj : type_proj >-> Vector.hom.
Coercion sort_proj1 : type_proj1 >-> Vector.hom.
Canonical herm_subType.
Canonical herm_eqType.
Canonical herm_choiceType.
Canonical psd_subType.
Canonical psd_eqType.
Canonical psd_choiceType.
Canonical den_subType.
Canonical den_eqType.
Canonical den_choiceType.
Canonical obs_subType.
Canonical obs_eqType.
Canonical obs_choiceType.
Canonical unitary_subType.
Canonical unitary_eqType.
Canonical unitary_choiceType.
Canonical den1_subType.
Canonical den1_eqType.
Canonical den1_choiceType.
Canonical proj_subType.
Canonical proj_eqType.
Canonical proj_choiceType.
Canonical proj1_subType.
Canonical proj1_eqType.
Canonical proj1_choiceType.
Canonical denf_unlockable.
Canonical psdf_unlockable.
Canonical obsf_unlockable.
Canonical unitaryf_unlockable.
Canonical den1f_unlockable.
Canonical projf_unlockable.
Canonical proj1f_unlockable.
Notation Hermlfun DO    := (hermf_of_lfun hermf_key DO).
Notation Psdlfun DO     := (psdf_of_lfun psdf_key DO).
Notation Denlfun DO     := (denf_of_lfun denf_key DO).
Notation Obslfun DO     := (obsf_of_lfun obsf_key DO).
Notation Unitarylfun DO := (unitaryf_of_lfun unitaryf_key DO).
Notation Den1lfun DO    := (den1f_of_lfun den1f_key DO).
Notation Projlfun DO    := (projf_of_lfun projf_key DO).
Notation Proj1lfun DO   := (proj1f_of_lfun proj1f_key DO).
Notation HermfType M    := (@Pack_herm _ (Phant _) _ M).
Notation PsdfType M     := (@Pack_psd _ (Phant _) _ M).
Notation DenfType M     := (@Pack_den _ (Phant _) _ M).
Notation ObsfType M     := (@Pack_obs _ (Phant _) _ M).
Notation UnitaryfType M := (@Pack_unitary _ (Phant _) _ M).
Notation Den1fType M    := (@Pack_den1 _ (Phant _) _ M).
Notation ProjfType M    := (@Pack_proj _ (Phant _) _ M).
Notation Proj1fType M   := (@Pack_proj1 _ (Phant _) _ M).
(* ?? needed or not ?? *)
Notation HermfVType V M    := (@Pack_herm _ (Phant V) _ M).
Notation PsdfVType V M     := (@Pack_psd _ (Phant V) _ M).
Notation DenfVType V M     := (@Pack_den _ (Phant V) _ M).
Notation ObsfVType V M     := (@Pack_obs _ (Phant V) _ M).
Notation UnitaryfVType V M := (@Pack_unitary _ (Phant V) _ M).
Notation Den1fVType V M    := (@Pack_den1 _ (Phant V) _ M).
Notation ProjfVType V M    := (@Pack_proj _ (Phant V) _ M).
Notation Proj1fVType V M   := (@Pack_proj1 _ (Phant V) _ M).
Notation "''FH' ( V )"  := (type_herm (Phant V)).
Notation "''F+' ( V )"  := (type_psd (Phant V)).
Notation "''FD' ( V )"  := (type_den (Phant V)).
Notation "''FO' ( V )"  := (type_obs (Phant V)).
Notation "''FU' ( V )"  := (type_unitary (Phant V)).
Notation "''FD1' ( V )" := (type_den1 (Phant V)).
Notation "''FP' ( V )"  := (type_proj (Phant V)).
Notation "''FP1' ( V )" := (type_proj1 (Phant V)).
Notation "''FH'"  := ('FH(_))  (only parsing) : type_scope.
Notation "''F+'"  := ('F+(_))  (only parsing) : type_scope.
Notation "''FD'"  := ('FD(_))  (only parsing) : type_scope.
Notation "''FO'"  := ('FO(_))  (only parsing) : type_scope.
Notation "''FU'"  := ('FU(_))  (only parsing) : type_scope.
Notation "''FD1'" := ('FD1(_)) (only parsing) : type_scope.
Notation "''FP'"  := ('FP(_))  (only parsing) : type_scope.
Notation "''FP1'" := ('FP1(_)) (only parsing) : type_scope.
Notation "''FH[' H ]_ S"  := (type_herm (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "''F+[' H ]_ S"  := (type_psd (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "''FD[' H ]_ S"  := (type_den (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "''FO[' H ]_ S"  := (type_obs (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "''FU[' H ]_ S"  := (type_unitary (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "''FD1[' H ]_ S" := (type_den1 (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "''FP[' H ]_ S"  := (type_proj (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "''FP1[' H ]_ S" := (type_proj1 (Phant 'H[H]_S)) (only parsing) : type_scope.
Notation "[ 'herm' 'of' f 'as' g ]" := (@clone_herm _ _ f g _ idfun) : form_scope.
Notation "[ 'herm' 'of' f ]" := (@clone_herm _ _ f _ _ id) : form_scope.
Notation "[ 'psd' 'of' f 'as' g ]" := (@clone_psd _ _ f g _ idfun) : form_scope.
Notation "[ 'psd' 'of' f ]" := (@clone_psd _ _ f _ _ id) : form_scope.
Notation "[ 'den' 'of' f 'as' g ]" := (@clone_den _ _ f g _ idfun) : form_scope.
Notation "[ 'den' 'of' f ]" := (@clone_den _ _ f _ _ id) : form_scope.
Notation "[ 'obs' 'of' f 'as' g ]" := (@clone_obs _ _ f g _ idfun) : form_scope.
Notation "[ 'obs' 'of' f ]" := (@clone_obs _ _ f _ _ id) : form_scope.
Notation "[ 'unitary' 'of' f 'as' g ]" := (@clone_unitary _ _ f g _ idfun) : form_scope.
Notation "[ 'unitary' 'of' f ]" := (@clone_unitary _ _ f _ _ id) : form_scope.
Notation "[ 'den1' 'of' f 'as' g ]" := (@clone_den1 _ _ f g _ idfun) : form_scope.
Notation "[ 'den1' 'of' f ]" := (@clone_den1 _ _ f _ _ id) : form_scope.
Notation "[ 'proj' 'of' f 'as' g ]" := (@clone_proj _ _ f g _ idfun) : form_scope.
Notation "[ 'proj' 'of' f ]" := (@clone_proj _ _ f _ _ id) : form_scope.
Notation "[ 'proj1' 'of' f 'as' g ]" := (@clone_proj1 _ _ f g _ idfun) : form_scope.
Notation "[ 'proj1' 'of' f ]" := (@clone_proj1 _ _ f _ _ id) : form_scope.
Definition hermfE := hermfE.
Definition psdfE := psdfE.
Definition denfE := denfE.
Definition obsfE := obsfE.
Definition unitaryfE := unitaryfE.
Definition den1fE := den1fE.
Definition projfE := projfE.
Definition proj1fE := proj1fE.

End Exports.

End LfunPred.
Include LfunPred.Exports.

Section LfunPredHierachy.
Variable (V: chsType).

Lemma hermf_herm (f : 'FH(V)) : (f : 'End(V)) \is hermlf.
Proof. by destruct f. Qed.

Lemma psdf_psd (f : 'F+(V)) : (f : 'End(V)) \is psdlf.
Proof. by destruct f. Qed.
Lemma psdf_herm (f : 'F+(V)) : (f : 'End(V)) \is hermlf.
Proof. by apply/psdlf_herm/psdf_psd. Qed.

Lemma denf_den (f : 'FD(V)) : (f : 'End(V)) \is denlf.
Proof. by destruct f. Qed.
Lemma denf_psd (f : 'FD(V)) : (f : 'End(V)) \is psdlf.
Proof. by apply/denlf_psd/denf_den. Qed.
Lemma denf_obs (f : 'FD(V)) : (f : 'End(V)) \is obslf.
Proof. by apply/denlf_obs/denf_den. Qed.
Lemma denf_herm (f : 'FD(V)) : (f : 'End(V)) \is hermlf.
Proof. by apply/denlf_herm/denf_den. Qed.

Lemma obsf_obs (f : 'FO(V)) : (f : 'End(V)) \is obslf.
Proof. by destruct f. Qed.
Lemma obsf_psd (f : 'FO(V)) : (f : 'End(V)) \is psdlf.
Proof. by apply/obslf_psd/obsf_obs. Qed.
Lemma obsf_herm (f : 'FO(V)) : (f : 'End(V)) \is hermlf.
Proof. by apply/obslf_herm/obsf_obs. Qed.

Lemma den1f_den1 (f : 'FD1(V)) : (f : 'End(V)) \is den1lf.
Proof. by destruct f. Qed.
Lemma den1f_den (f : 'FD1(V)) : (f : 'End(V)) \is denlf.
Proof. by apply/den1lf_den/den1f_den1. Qed.
Lemma den1f_psd (f : 'FD1(V)) : (f : 'End(V)) \is psdlf.
Proof. by apply/den1lf_psd/den1f_den1. Qed.
Lemma den1f_obs (f : 'FD1(V)) : (f : 'End(V)) \is obslf.
Proof. by apply/den1lf_obs/den1f_den1. Qed.
Lemma den1f_herm (f : 'FD1(V)) : (f : 'End(V)) \is hermlf.
Proof. by apply/den1lf_herm/den1f_den1. Qed.

Lemma projf_proj (f : 'FP(V)) : (f : 'End(V)) \is projlf.
Proof. by destruct f. Qed.
Lemma projf_psd (f : 'FP(V)) : (f : 'End(V)) \is psdlf.
Proof. by apply/projlf_psd/projf_proj. Qed.
Lemma projf_obs (f : 'FP(V)) : (f : 'End(V)) \is obslf.
Proof. by apply/projlf_obs/projf_proj. Qed.
Lemma projf_herm (f : 'FP(V)) : (f : 'End(V)) \is hermlf.
Proof. by apply/projlf_herm/projf_proj. Qed.

Lemma proj1f_proj1 (f : 'FP1(V)) : (f : 'End(V)) \is proj1lf.
Proof. by destruct f. Qed.
Lemma proj1f_proj (f : 'FP1(V)) : (f : 'End(V)) \is projlf.
Proof. by apply/proj1lf_proj/proj1f_proj1. Qed.
Lemma proj1f_den1 (f : 'FP1(V)) : (f : 'End(V)) \is den1lf.
Proof. by apply/proj1lf_den1/proj1f_proj1. Qed.
Lemma proj1f_den (f : 'FP1(V)) : (f : 'End(V)) \is denlf.
Proof. by apply/proj1lf_den/proj1f_proj1. Qed.
Lemma proj1f_psd (f : 'FP1(V)) : (f : 'End(V)) \is psdlf.
Proof. by apply/proj1lf_psd/proj1f_proj1. Qed.
Lemma proj1f_obs (f : 'FP1(V)) : (f : 'End(V)) \is obslf.
Proof. by apply/proj1lf_obs/proj1f_proj1. Qed.
Lemma proj1f_herm (f : 'FP1(V)) : (f : 'End(V)) \is hermlf.
Proof. by apply/proj1lf_herm/proj1f_proj1. Qed.

Lemma unitaryf_unitary (f : 'FU(V)) : (f : 'End(V)) \is unitarylf.
Proof. by destruct f. Qed.

Canonical psdf_hermfType   (f : 'F+(V))   := HermfType (psdf_herm f).
Canonical denf_psdfType    (f : 'FD(V))   := PsdfType (denf_psd f).
Canonical denf_obsfType    (f : 'FD(V))   := ObsfType (denf_obs f).
Canonical denf_hermfType   (f : 'FD(V))   := HermfType (denf_herm f).
Canonical obsf_psdfType    (f : 'FO(V))   := PsdfType (obsf_psd f).
Canonical obsf_hermfType   (f : 'FO(V))   := HermfType (obsf_herm f).
Canonical den1f_psdfType   (f : 'FD1(V))  := PsdfType (den1f_psd f).
Canonical den1f_denfType   (f : 'FD1(V))  := DenfType (den1f_den f).
Canonical den1f_obsfType   (f : 'FD1(V))  := ObsfType (den1f_obs f).
Canonical den1f_hermfType  (f : 'FD1(V))   := HermfType (den1f_herm f).
Canonical projf_psdfType   (f : 'FP(V))  := PsdfType (projf_psd f).
Canonical projf_obsfType   (f : 'FP(V))  := ObsfType (projf_obs f).
Canonical projf_hermfType  (f : 'FP(V))  := HermfType (projf_herm f).
Canonical proj1f_psdfType  (f : 'FP1(V)) := PsdfType (proj1f_psd f).
Canonical proj1f_denfType  (f : 'FP1(V)) := DenfType (proj1f_den f).
Canonical proj1f_obsfType  (f : 'FP1(V)) := ObsfType (proj1f_obs f).
Canonical proj1f_den1fType (f : 'FP1(V)) := Den1fType (proj1f_den1 f).
Canonical proj1f_projfType (f : 'FP1(V)) := ProjfType (proj1f_proj f).
Canonical proj1f_hermfType (f : 'FP1(V)) := HermfType (proj1f_herm f).

Lemma hermfP (f g : 'FH(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed.
Lemma psdfP (f g : 'F+(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed.
Lemma denfP (f g : 'FD(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed.
Lemma obsfP (f g : 'FO(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed. 
Lemma unitaryfP (f g : 'FU(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed. 
Lemma den1fP (f g : 'FD1(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed.
Lemma projfP (f g : 'FP(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed.
Lemma proj1fP (f g : 'FP1(V)) : (f : 'End(V)) = (g : 'End(V)) <-> f = g.
Proof. split=>[|->//]; apply/val_inj. Qed.

End LfunPredHierachy.

Section LfpredTensor.
Variable (V: chsType) (A : 'End(V)).

Lemma lf_psd_decomp :
  exists (M1 M2 M3 M4 : 'End(V)) , M1 \is psdlf /\ M2 \is psdlf 
  /\ M3 \is psdlf /\ M4 \is psdlf /\ A = M1 - M2 + 'i *: M3 - 'i *: M4.
Proof.
move: (mx_psd_decomp (f2mx A))=>[M1 [M2 [M3 [M4]]]] [P1 [P2 [P3 [P4]]]] P5.
exists (Vector.Hom M1). exists (Vector.Hom M2). exists (Vector.Hom M3).
exists (Vector.Hom M4). do ? split.
1,2,3,4: by rewrite qualifE/= ?P1 ?P2 ?P3 ?P4.
apply/f2mx_inj. by rewrite P5 !linearD/= !linearN/= !linearZ/=.
Qed.

Lemma hermlfP : reflect (A^A = A) (A \is hermlf).
Proof.
rewrite qualifE; apply/(iffP idP)=>[/hermmxP P|/(f_equal f2mx)/=/esym/hermmxP//].
by apply/f2mx_inj; rewrite/= -P.
Qed.

Lemma hermlfE : (A \is hermlf) = (A^A == A).
Proof. by apply/eqb_iff; split=>[/hermlfP/eqP->|/eqP/hermlfP]. Qed.

Lemma psdlfP : 
  reflect (forall v, [< v ; A v>] >= 0) (A \is psdlf). 
Proof.
apply (iffP idP); rewrite qualifE -psdmx_tr.
move=>/psdmx_dot P v. move: P =>/(_ (v2r v)^*m).
2: move=>P; apply/psdmx_dot=>u; move: (P (r2v u)^*v)%VF.
all: by rewrite nnegrE dotp_mulmx unlock/= !r2vK trmx_mul 
  adjmxEl ?conjmxK trace_mx11 mulmxA.
Qed.

Lemma hermlf_trlf : A \is hermlf -> \Tr A \is Num.real.
Proof.
rewrite qualifE=>P1; rewrite lftrace_baseE; apply/sum_real=>i _.
move: P1=>/hermmx_dot/(_ (v2r (eb i))).
by rewrite dotp_mulmx/= -mxtrace_tr !trmx_mul trace_mx11 unlock/= r2vK trmx_mul adjmxEl trmxK.
Qed.

Lemma psdlf_trlf : A \is psdlf -> 0 <= \Tr A.
Proof. by move/psdlfP=>P; rewrite lftrace_baseE sumr_ge0. Qed.

Lemma denlfP : reflect (A \is psdlf /\ \Tr A <= 1) (A \is denlf). 
Proof. by rewrite qualifE [_ \is denlf]qualifE /lftrace; apply (iffP (denmxP _)). Qed.

Lemma denlf_trlf : A \is denlf -> \Tr A <= 1.
Proof. by move=>/denlfP[]. Qed.

Lemma obslfP : 
  reflect (A \is psdlf /\ forall u, [<u ; A u>] <= [< u; u >]) (A \is obslf). 
Proof.
rewrite [X in reflect _ X]qualifE -obsmx_tr.
apply (iffP (obsmx_dot _))=>[P|[/psdlfP P1 P2 u]].
split. apply/psdlfP. 1,2: move=>v; move: (P (v2r v)^*m)%VF=>/andP.
3: apply/andP; move: (P1 (r2v u)^*v)%VF (P2 (r2v u)^*v)%VF.
all: rewrite !dotp_mulmx unlock/= !r2vK trmx_mul 
  adjmxEl ?conjmxK !trace_mx11 mulmxA.
by move=>[->]. by move=>[_->]. by split.
Qed.

Lemma unitarylfP : reflect (A^A \o A = \1) (A \is unitarylf).
Proof. 
rewrite qualifE; apply/(iffP (@unitarymxP _ _ _ _))=>[P|/(f_equal f2mx)].
apply/f2mx_inj. all: by rewrite f2mx_comp /adj_lfun/= f2mx1 adjmxE.
Qed.

Lemma unitarylfPV : reflect (A \o A^A = \1) (A \is unitarylf).
Proof.
rewrite qualifE; apply/(iffP (@unitarymxPV _ _ _))=>[P|/(f_equal f2mx)].
apply/f2mx_inj. all: by rewrite f2mx_comp /adj_lfun/= f2mx1 adjmxE.
Qed.

Lemma unitarylf_dotP : 
  reflect (forall u, [< A u ; A u>] = [< u; u >]) (A \is unitarylf). 
Proof.
have P0 n : (1%:M : 'M[C]_n) = (1%:M)^*m by apply/matrixP=>i j; rewrite !mxE conjC_nat.
rewrite qualifE. apply (iffP (@unitarymxP _ _ _ _))=>[P u|P].
rewrite !dotp_mulmx unlock/= !r2vK conjmxM trmx_mul !mulmxA.
do ? f_equal. rewrite -mulmxA -[RHS]mulmx1. f_equal.
by apply/conjmx_inj; rewrite conjmxM conjmxK conjmx1 -adjmxEr adjmxE P.
apply/conjmx_inj. rewrite -P0.
apply/subr0_eq/eqP/mx_dot_eq0=>u; rewrite linearB/= mulmxBl linearB/= mulmx1. 
apply/eqP. rewrite subr_eq0. apply/eqP. move: (P (r2v u)^*v)%VF.
by rewrite !dotp_mulmx unlock/= !r2vK !conjmx_map !trmx_mul !conjmxM 
  !conjmxK !trace_mx11 !mulmxA adjmxEl.
Qed.

Lemma idemr_01 (T : fieldType) (x : T) : 
  (x ^+2 == x) = ((x == 0) || (x == 1)).
Proof. by rewrite -subr_eq0 -{2}(mul1r x) -mulrBl mulf_eq0 subr_eq0 orbC. Qed.

Lemma boolmx_dmul (T : numClosedFieldType) m n (M : 'M[T]_(m,n)) :
  M \is a boolmx <-> M .* M = M.
split.
move=>/boolmxP P; apply/matrixP=> i j; rewrite mxE.
by move: (P i j); rewrite -idemr_01 expr2=>/eqP.
move=>/matrixP P; apply/boolmxP=> i j.
by move: (P i j)=>/eqP; rewrite mxE -expr2 idemr_01.
Qed.

Lemma projmxP_id (T : numClosedFieldType) m (B : 'M[T]_m) : 
reflect (B \is hermmx /\ (B *m B = B)) (B \is projmx).
Proof.
apply(iffP (projmxP _))=>[[P1 P2]|[P1 P2]]; split=>//.
move: P1=>/hermmx_normal/unitarymx_spectralP P1.
rewrite P1 !mulmxA mulmxtVK ?spectral_unitarymx//. f_equal.
rewrite -mulmxA. f_equal.
by move/boolmx_dmul: P2; rewrite diag_mx_dmul=>->.
move: P1=>/hermmx_normal/unitarymx_spectralP P1.
move: (spectral_unitarymx B) P2=>Q.
rewrite {1 2 3}P1 !mulmxA mulmxtVK// mulmxU// mulmxtVK// -mulmxA mulUCmx//.
by rewrite mulmxA unitarymxK// mul1mx diag_mx_dmul=>/diag_mx_inj/boolmx_dmul.
Qed.

Lemma projlfP : reflect (A^A = A /\ (A \o A = A)) (A \is projlf).
Proof.
apply(iffP idP)=>[H0|[/hermlfP P1 P2]].
split. by apply/hermlfP/projlf_herm.
by apply/f2mx_inj; rewrite f2mx_comp; move: H0; rewrite qualifE=>/projmxP_id[_ ].
rewrite qualifE; apply/projmxP_id; split.
by move: P1; rewrite qualifE.
by move: P2=>/(f_equal f2mx); rewrite f2mx_comp.
Qed.

Lemma projlf_psdP : reflect (A \is psdlf /\ (A \o A = A)) (A \is projlf).
Proof.
apply(iffP idP)=>[H0|[P1 P2]].
by split; [apply/projlf_psd | move: H0=>/projlfP[]].
by apply/projlfP; split=>//; apply/hermlfP/psdlf_herm.
Qed.

Lemma den1lfP : reflect (A \is psdlf /\ \Tr A = 1) (A \is den1lf).
Proof. apply(iffP idP).
by rewrite qualifE=>/den1mxP=>[[P1 /eqP P2]]; split=>[|//]; rewrite qualifE.
by rewrite qualifE /lftrace=>[[P1 P2]]; rewrite qualifE; apply/den1mxP; split=>//; apply/eqP.
Qed.

End LfpredTensor.

Section LFunRank.
Implicit Type (U V : chsType).

Definition lfrank U V (A : 'Hom(U,V)) := \rank (f2mx A).
Notation "\Rank A" := (lfrank A).

Lemma mxrank_mulmxU (T : numClosedFieldType) m n (A : 'M[T]_(m,n)) (U : 'M[T]_n) :
  U \is unitarymx -> \rank (A *m U) = \rank A.
Proof. move=>/mxrank_unitary P1; by rewrite mxrankMfree// /row_free P1. Qed.

Lemma mxrank_mulUmx (T : numClosedFieldType) m n (U : 'M[T]_m) (A : 'M[T]_(m,n)) :
  U \is unitarymx -> \rank (U *m A) = \rank A.
Proof.
by move=>P; rewrite -mxrank_tr trmx_mul mxrank_mulmxU ?trmx_unitary// mxrank_tr.
Qed.

Lemma mxrank_mulmxUC (T : numClosedFieldType) m n (A : 'M[T]_(m,n)) (U : 'M[T]_n) :
  U \is unitarymx -> \rank (A *m U^*t) = \rank A.
Proof. by move=>P; rewrite mxrank_mulmxU// trmxC_unitary. Qed.

Lemma mxrank_mulUCmx (T : numClosedFieldType) m n (U : 'M[T]_m) (A : 'M[T]_(m,n)) :
  U \is unitarymx -> \rank (U^*t *m A) = \rank A.
Proof. by move=>P; rewrite mxrank_mulUmx// trmxC_unitary. Qed.

Lemma ranklfU U V (A : 'Hom(U,V)) (B : 'End(U)) :
  B \is unitarylf -> \Rank (A \o B) = \Rank A.
Proof. by rewrite qualifE=>P1; rewrite /lfrank f2mx_comp mxrank_mulUmx. Qed.

Lemma rankUlf U V (A : 'Hom(U,V)) (B : 'End(V)) :
  B \is unitarylf -> \Rank (B \o A) = \Rank A.
Proof. by rewrite qualifE=>P1; rewrite /lfrank f2mx_comp mxrank_mulmxU. Qed.

Lemma ranklf_adj U V (A : 'Hom(U,V)) : \Rank (A^A) = \Rank A.
Proof. by rewrite /lfrank/= mxrank_map mxrank_tr. Qed.

Lemma ranklf_conj U V (A : 'Hom(U,V)) : \Rank (A^C) = \Rank A.
Proof. by rewrite /lfrank/= mxrank_map. Qed.

Lemma ranklf_tr U V (A : 'Hom(U,V)) : \Rank (A^T) = \Rank A.
Proof. by rewrite /lfrank/= mxrank_tr. Qed.

Lemma ranklf0 U V : \Rank (0 : 'Hom(U,V)) = 0%N.
Proof. by rewrite /lfrank linear0 mxrank0. Qed.

Lemma ranklf1 U : \Rank (\1 : 'End(U)) = Vector.dim U.
Proof. by rewrite /lfrank f2mx1 mxrank1. Qed.

End LFunRank.

Notation "\Rank A" := (lfrank A) : lfun_scope.

Section Projlf.
Variable (H : chsType).

Lemma psdf_trlf (A : 'F+(H)) : 0 <= \Tr A.
Proof. apply/psdlf_trlf/psdf_psd. Qed.

Lemma denf_trlf (A : 'FD(H)) : \Tr A <= 1.
Proof. apply/denlf_trlf/denf_den. Qed.

Lemma den1lf_trlf (A : 'End(H)) : A \is den1lf -> \Tr A = 1.
Proof. by move=>/den1lfP[]. Qed.
Lemma den1f_trlf (A : 'FD1(H)) : \Tr A = 1.
Proof. by apply/den1lf_trlf/den1f_den1. Qed.

Lemma projmx_tr (T : numClosedFieldType) m (A : 'M[T]_m) : 
  A \is projmx -> \tr A = (\rank A)%:R.
Proof.
move=>/projmxP[/hermmx_normal/unitarymx_spectralP P1 /boolmxP P2].
move: (spectral_unitarymx A)=>Q.
rewrite P1 mxtrace_mulC mulmxA unitarymxK// mul1mx mxrank_mulmxU// mxrank_mulUCmx//.
rewrite rank_diagmx mxtrace_diag natr_sum; apply eq_bigr=>i _.
by move: (P2 ord0 i)=>/orP[/eqP->|/eqP->]; rewrite ?oner_neq0// eqxx.
Qed.

Lemma projlf_trlf (A : 'End(H)) : A \is projlf -> \Tr A = (\Rank A)%:R.
Proof. by rewrite qualifE=>/projmx_tr. Qed.

Lemma projf_trlf (A : 'FP(H)) : \Tr A = (\Rank A)%:R.
Proof. apply/projlf_trlf/projf_proj. Qed.

Lemma proj1lf_rankP (A : 'End(H)) : 
  reflect (A \is projlf /\ \Rank A = 1%N) (A \is proj1lf).
Proof.
rewrite qualifE /lfrank [X in reflect _ X]qualifE.
by apply/(iffP (proj1mxP _))=>[[P1 /eqP]|[P1 P2]]; split=>//; apply/eqP.
Qed.

Lemma proj1lfP (A : 'End(H)) : 
  reflect (A \is projlf /\ \Tr A = 1) (A \is proj1lf).
Proof.
apply/(iffP (proj1lf_rankP _))=>[[P1 P2]|[P1/eqP P2]]; split=>//.
by rewrite projlf_trlf// P2. by move: P2; rewrite projlf_trlf// pnatr_eq1=>/eqP.
Qed.

Lemma hermlf_adjE (P : 'End(H)) : P \is hermlf -> P^A = P.
Proof. by move=>/hermlfP. Qed.

Lemma hermf_adjE (P : 'FH(H)) : P^A = P.
Proof. apply/hermlf_adjE/hermf_herm. Qed.

Lemma projlf_idem (A : 'End(H)) : A \is projlf -> A \o A = A.
Proof. by move=>/projlfP[]. Qed.

Lemma projf_idem (A : 'FP(H)) : A \o A = A.
Proof. apply/projlf_idem/projf_proj. Qed.

Lemma projlf_idemE (A : 'FP(H)) x : A (A x) = A x.
Proof. by rewrite -[in RHS]projf_idem lfunE. Qed.

Lemma hermlf_dotE (P : 'End(H)) x y : P \is hermlf -> [< P x ; y >] = [< x ; P y >].
Proof. by move=>/hermlf_adjE; rewrite adj_dotE=>->. Qed.

Lemma hermf_dotE (P : 'FH(H)) x y : [< P x ; y >] = [< x ; P y >].
Proof. by rewrite adj_dotE hermf_adjE. Qed.

Lemma projf_dot (P : 'FP(H)) x : [< x ; P x >] = `|P x|^+2.
Proof. by rewrite -dotp_norm -adj_dotEV hermf_adjE/= -comp_lfunE projf_idem. Qed.

Lemma projlf_dot (P : 'End(H)) x : P \is projlf -> [< x ; P x >] = `|P x|^+2.
Proof. move=>P1; rewrite -(projfE tt P1); exact: projf_dot. Qed.

Lemma proj1lf_trlf (P : 'End(H)) : P \is proj1lf -> \Tr P = 1.
Proof. by move=>/proj1lfP[]. Qed.
Lemma proj1f_trlf (P : 'FP1(H)) : \Tr P = 1.
Proof. apply/proj1lf_trlf/proj1f_proj1. Qed.

Lemma proj1lf_rank (P : 'End(H)) : P \is proj1lf -> \Rank P = 1%N.
Proof. by move=>/proj1lf_rankP[]. Qed.
Lemma proj1f_rank (P : 'FP1(H)) : \Rank P = 1%N.
Proof. apply/proj1lf_rank/proj1f_proj1. Qed.

End Projlf.

Section DefaultDenObs.
Variable (V: chsType).

Lemma hermlf_adj (A:'End(V)) : A^A \is hermlf = (A \is hermlf).
Proof. by rewrite !hermlfE adjfK eq_sym. Qed.
Lemma hermlf_tr (A:'End(V)) : A^T \is hermlf = (A \is hermlf).
Proof. by rewrite !hermlfE lfTAC (can_eq (@trfK _ _)). Qed.
Lemma hermlf_conj (A:'End(V)) : A^C \is hermlf = (A \is hermlf).
Proof. by rewrite conjfAT hermlf_tr hermlf_adj. Qed.

Lemma hermlf0 : (0 : 'End(V)) \is hermlf.
Proof. by apply/hermlfP; rewrite raddf0. Qed.
Lemma hermlf1 : (\1 : 'End(V)) \is hermlf.
Proof. by apply/hermlfP; rewrite adjf1. Qed.

Lemma hermlfD (A B : 'End(V)) : A \is hermlf -> B \is hermlf -> A + B \is hermlf.
Proof. by move=>/hermlfP P1/hermlfP P2; apply/hermlfP; rewrite adjfD P1 P2. Qed.
Lemma hermlfN (A : 'End(V)) : - A \is hermlf = (A \is hermlf).
Proof. by rewrite !hermlfE raddfN/= eqr_opp. Qed.
Lemma hermlf_sum I (r : seq I) (P : pred I) (f : I -> 'End(V)) :
  (forall i, P i -> f i \is hermlf) -> \sum_(i <- r | P i) f i \is hermlf.
Proof.
move=>IH; elim: r=>[|r i IH1]; first by rewrite big_nil hermlf0.
by rewrite big_cons; case E: (P r)=>[|//]; apply hermlfD=>[|//]; apply IH.
Qed.

Lemma psdlf_adj (A:'End(V)) : A^A \is psdlf = (A \is psdlf).
Proof.
by apply/eqb_iff; split=>/psdlfP P; apply/psdlfP=>v; 
move: (P v); rewrite adj_dotEV -conj_dotp conjC_ge0.
Qed.
Lemma psdlf_conj (A:'End(V)) : A^C \is psdlf = (A \is psdlf).
Proof.
by apply/eqb_iff; split=>/psdlfP P; apply/psdlfP=>v; [move: (P v^*v) 
  | rewrite -(conjvK v)]; rewrite conjfEV conjv_dot -conj_dotp conjC_ge0.
Qed.
Lemma psdlf_tr (A:'End(V)) : A^T \is psdlf = (A \is psdlf).
Proof. by rewrite trfAC psdlf_conj psdlf_adj. Qed.

Lemma Re_conj (x : C) : Re (x^*) = Re x.
Proof. by destruct x. Qed.

Lemma Im_conj (x : C) : Im (x^*) = - Im x.
Proof. by destruct x. Qed.

Lemma lec_conj (x y : C) : x^* <= y^* = (x <= y).
Proof. by rewrite !lecE/= !Re_conj !Im_conj eqr_opp. Qed.

Lemma denlf_adj (A:'End(V)) : A^A \is denlf = (A \is denlf).
Proof.
by apply/eqb_iff; split=>/denlfP P; apply/denlfP; move: P;
rewrite psdlf_adj lftrace_adj -[X in _^* <= X]conjC1 lec_conj.
Qed.
Lemma denlf_tr (A:'End(V)) : A^T \is denlf = (A \is denlf).
Proof.
apply/eqb_iff; split=>/denlfP P; apply/denlfP; move: P;
by rewrite psdlf_tr lftrace_tr.
Qed.
Lemma denlf_conj (A:'End(V)) : A^C \is denlf = (A \is denlf).
Proof. by rewrite conjfAT denlf_tr denlf_adj. Qed.

Lemma obslf_adj (A:'End(V)) : A^A \is obslf = (A \is obslf).
Proof.
by apply/eqb_iff; split=>/obslfP [P1 P2]; apply/obslfP; move: P1 P2;
rewrite psdlf_adj; split=>// =>u; move: (P2 u); rewrite adj_dotEV -conj_dotp
-[X in _ <= X -> _]conj_dotp lec_conj.
Qed.
Lemma obslf_tr (A:'End(V)) : A^T \is obslf = (A \is obslf).
Proof. by rewrite qualifE/= obsmx_tr [RHS]qualifE. Qed.
Lemma obslf_conj (A:'End(V)) : A^C \is obslf = (A \is obslf).
Proof. by rewrite conjfAT obslf_tr obslf_adj. Qed.

Lemma unitarylf_comp (A B : 'End(V)): 
  A \is unitarylf -> B \is unitarylf -> A \o B \is unitarylf.
Proof.
by move=>/unitarylfP PA /unitarylfP PB; apply/unitarylfP; 
rewrite adjf_comp !comp_lfunA comp_lfunACA PA comp_lfun1r.
Qed.
Lemma unitarylf_adj (A:'End(V)) : A^A \is unitarylf = (A \is unitarylf).
Proof. by rewrite qualifE/= [RHS]qualifE trmxC_unitary. Qed.
Lemma unitarylf_tr (A:'End(V)) : A^T \is unitarylf = (A \is unitarylf).
Proof. by rewrite qualifE/= [RHS]qualifE trmx_unitary. Qed.
Lemma unitarylf_conj (A:'End(V)) : A^C \is unitarylf = (A \is unitarylf).
Proof. by rewrite conjfAT unitarylf_tr unitarylf_adj. Qed.

Lemma den1lf_adj (A:'End(V)) : A^A \is den1lf = (A \is den1lf).
Proof.
apply/eqb_iff; split=>/den1lfP P; apply/den1lfP; move: P;
by rewrite psdlf_adj lftrace_adj=>[[->/(f_equal conjC)]]; rewrite ?conjCK conjC1.
Qed.
Lemma den1lf_tr (A:'End(V)) : A^T \is den1lf = (A \is den1lf).
Proof.
apply/eqb_iff; split=>/den1lfP P; apply/den1lfP; move: P;
by rewrite psdlf_tr lftrace_tr.
Qed.
Lemma den1lf_conj (A:'End(V)) : A^C \is den1lf = (A \is den1lf).
Proof. by rewrite conjfAT den1lf_tr den1lf_adj. Qed.

Lemma projlf_adj (A:'End(V)) : A^A \is projlf = (A \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP; rewrite ?adjfK=>[[P1 P2]]; apply/projlfP; 
by split; apply/adjf_inj; rewrite ?adjf_comp ?adjfK.
Qed.
Lemma projlf_tr (A:'End(V)) : A^T \is projlf = (A \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP[P1 P2]; apply/projlfP;
by split; apply/trf_inj; rewrite ?trf_comp ?lfATC ?trfK.
Qed.
Lemma projlf_conj (A:'End(V)) : A^C \is projlf = (A \is projlf).
Proof. by rewrite conjfAT projlf_tr projlf_adj. Qed.

Lemma proj1lf_adj (A:'End(V)) : A^A \is proj1lf = (A \is proj1lf).
Proof.
apply/eqb_iff; split=>/proj1lf_rankP P; apply/proj1lf_rankP; 
by move: P; rewrite projlf_adj ranklf_adj.
Qed.
Lemma proj1lf_tr (A:'End(V)) : A^T \is proj1lf = (A \is proj1lf).
Proof.
apply/eqb_iff; split=>/proj1lf_rankP P; apply/proj1lf_rankP; 
by move: P; rewrite projlf_tr ranklf_tr.
Qed.
Lemma proj1lf_conj (A:'End(V)) : A^C \is proj1lf = (A \is proj1lf).
Proof. by rewrite conjfAT proj1lf_tr proj1lf_adj. Qed.

Lemma hermf_adj (A : 'FH(V)) : A^A \is hermlf.
Proof. by rewrite hermlf_adj hermf_herm. Qed.
Canonical adj_hermfType A := HermfType (hermf_adj A).
Lemma hermf_tr (A : 'FH(V)) : A^T \is hermlf.
Proof. by rewrite hermlf_tr hermf_herm. Qed.
Canonical tr_hermfType A := HermfType (hermf_tr A).
Lemma hermf_conj (A : 'FH(V)) : A^C \is hermlf.
Proof. by rewrite hermlf_conj hermf_herm. Qed.
Canonical conj_hermfType A := HermfType (hermf_conj A).
Lemma hermfD (A B : 'FH(V)) : A%:VF + B \is hermlf.
Proof. apply/hermlfD; apply/hermf_herm. Qed.
Canonical add_hermfType A B := HermfType (hermfD A B).
Lemma hermfN (A : 'FH(V)) : - A%:VF \is hermlf.
Proof. by rewrite hermlfN hermf_herm. Qed.
Canonical opp_hermfType A := HermfType (hermfN A).
Canonical zero_hermfType := HermfType hermlf0.
Canonical one_hermfType := HermfType hermlf1.

(* psdf_add : defined later *)
Lemma psdf_adj (A : 'F+(V)) : A^A \is psdlf.
Proof. by rewrite psdlf_adj psdf_psd. Qed.
Canonical adj_psdfType A := PsdfType (psdf_adj A).
Lemma psdf_conj (A : 'F+(V)) : A^C \is psdlf.
Proof. by rewrite psdlf_conj psdf_psd. Qed.
Canonical conj_psdfType A := PsdfType (psdf_conj A).
Lemma psdf_tr (A : 'F+(V)) : A^T \is psdlf.
Proof. by rewrite psdlf_tr psdf_psd. Qed.
Canonical tr_psdfType A := PsdfType (psdf_tr A).

Lemma denf_adj (A : 'FD(V)) : A^A \is denlf.
Proof. by rewrite denlf_adj denf_den. Qed.
Canonical adj_denfType A := DenfType (denf_adj A).
Lemma denf_conj (A : 'FD(V)) : A^C \is denlf.
Proof. by rewrite denlf_conj denf_den. Qed.
Canonical conj_denfType A := DenfType (denf_conj A).
Lemma denf_tr (A : 'FD(V)) : A^T \is denlf.
Proof. by rewrite denlf_tr denf_den. Qed.
Canonical tr_denfType A := DenfType (denf_tr A).

Lemma obsf_adj (A : 'FO(V)) : A^A \is obslf.
Proof. by rewrite obslf_adj obsf_obs. Qed.
Canonical adj_obsfType A := ObsfType (obsf_adj A).
Lemma obsf_conj (A : 'FO(V)) : A^C \is obslf.
Proof. by rewrite obslf_conj obsf_obs. Qed.
Canonical conj_obsfType A := ObsfType (obsf_conj A).
Lemma obsf_tr (A : 'FO(V)) : A^T \is obslf.
Proof. by rewrite obslf_tr obsf_obs. Qed.
Canonical tr_obsfType A := ObsfType (obsf_tr A).

Lemma unitaryf_comp (A B : 'FU(V)) : A \o B \is unitarylf.
Proof. apply/unitarylf_comp; apply/unitaryf_unitary. Qed.
Canonical comp_unitaryfType A B := UnitaryfType (unitaryf_comp A B).
Lemma unitaryf_adj (A : 'FU(V)) : A^A \is unitarylf.
Proof. by rewrite unitarylf_adj unitaryf_unitary. Qed.
Canonical adj_unitaryfType A := UnitaryfType (unitaryf_adj A).
Lemma unitaryf_conj (A : 'FU(V)) : A^C \is unitarylf.
Proof. by rewrite unitarylf_conj unitaryf_unitary. Qed.
Canonical conj_unitaryfType A := UnitaryfType (unitaryf_conj A).
Lemma unitaryf_tr (A : 'FU(V)) : A^T \is unitarylf.
Proof. by rewrite unitarylf_tr unitaryf_unitary. Qed.
Canonical tr_unitaryfType A := UnitaryfType (unitaryf_tr A).

Lemma den1f_adj (A : 'FD1(V)) : A^A \is den1lf.
Proof. by rewrite den1lf_adj den1f_den1. Qed.
Canonical adj_den1fType A := Den1fType (den1f_adj A).
Lemma den1f_conj (A : 'FD1(V)) : A^C \is den1lf.
Proof. by rewrite den1lf_conj den1f_den1. Qed.
Canonical conj_den1fType A := Den1fType (den1f_conj A).
Lemma den1f_tr (A : 'FD1(V)) : A^T \is den1lf.
Proof. by rewrite den1lf_tr den1f_den1. Qed.
Canonical tr_den1fType A := Den1fType (den1f_tr A).

Lemma projf_adj (A : 'FP(V)) : A^A \is projlf.
Proof. by rewrite projlf_adj projf_proj. Qed.
Canonical adj_projfType A := ProjfType (projf_adj A).
Lemma projf_conj (A : 'FP(V)) : A^C \is projlf.
Proof. by rewrite projlf_conj projf_proj. Qed.
Canonical conj_projfType A := ProjfType (projf_conj A).
Lemma projf_tr (A : 'FP(V)) : A^T \is projlf.
Proof. by rewrite projlf_tr projf_proj. Qed.
Canonical tr_projfType A := ProjfType (projf_tr A).

Lemma proj1f_adj (A : 'FP1(V)) : A^A \is proj1lf.
Proof. by rewrite proj1lf_adj proj1f_proj1. Qed.
Canonical adj_proj1fType A := Proj1fType (proj1f_adj A).
Lemma proj1f_conj (A : 'FP1(V)) : A^C \is proj1lf.
Proof. by rewrite proj1lf_conj proj1f_proj1. Qed.
Canonical conj_proj1fType A := Proj1fType (proj1f_conj A).
Lemma proj1f_tr (A : 'FP1(V)) : A^T \is proj1lf.
Proof. by rewrite proj1lf_tr proj1f_proj1. Qed.
Canonical tr_proj1fType A := Proj1fType (proj1f_tr A).

Lemma unitaryf_form (A : 'FU(V)) : A^A \o A = \1.
Proof. apply/unitarylfP/unitaryf_unitary. Qed.
Lemma unitaryf_formV (A : 'FU(V)) : A \o A^A = \1.
Proof. apply/unitarylfPV/unitaryf_unitary. Qed.

Lemma projlf1 : (\1 : 'End(V)) \is projlf.
Proof. by apply/projlfP; rewrite adjf1 comp_lfun1l. Qed.
Lemma obslf1 : (\1 : 'End(V)) \is obslf. Proof. apply/projlf_obs/projlf1. Qed. 
Lemma psdlf1 : (\1 : 'End(V)) \is psdlf. Proof. apply/projlf_psd/projlf1. Qed.
Lemma unitarylf1 : (\1 : 'End(V)) \is unitarylf.
Proof. by apply/unitarylfP; rewrite adjf1 comp_lfun1l. Qed.
Canonical one_projfType := ProjfType projlf1.
Canonical one_obsfType := ObsfType obslf1.
Canonical one_psdfType := PsdfType psdlf1.
Canonical one_unitaryfType := UnitaryfType unitarylf1.

Lemma projlf0 : (0 : 'End(V)) \is projlf.
Proof. by apply/projlfP; rewrite linear0 comp_lfun0l. Qed.
Lemma obslf0 : (0 : 'End(V)) \is obslf. Proof. apply/projlf_obs/projlf0. Qed. 
Lemma psdlf0 : (0 : 'End(V)) \is psdlf. Proof. apply/projlf_psd/projlf0. Qed.
Lemma denlf0 : (0 : 'End(V)) \is denlf.
Proof. by apply/denlfP; split; [apply/psdlf0 | rewrite linear0 ler01]. Qed.
Canonical zero_projfType := ProjfType projlf0.
Canonical zero_obsfType := ObsfType obslf0.
Canonical zero_psdfType := PsdfType psdlf0.
Canonical zero_denfType := DenfType denlf0.

End DefaultDenObs.

(* should build PONB -> ONB *)
(* do this later; e.g., canonical ONB as PONB*)
Module PONB.

Section ClassDef.
Variable (H : chsType) (F : finType).

Definition axiom (f : F -> H) := 
  (forall i j, [< f i ; f j >] = (i == j)%:R).

Structure map (phUV : phant (F -> H)) := Pack {
  apply; 
  _ : axiom apply; 
}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> H)) (f g : F -> H) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation ponbasis f := (axiom f).
Coercion apply : map >-> Funclass.
Notation PONBasis fA := (Pack (Phant _) fA).
Notation "''PONB' ( F ; S )" := (map (Phant (F -> S))) : type_scope.
Notation "''PONB[' H ]_ ( F ; S )" := (map (Phant (F -> 'H[H]_S))) : type_scope.
Notation "''PONB_' ( F ; S )" := ('PONB[_]_(F;S)) : type_scope.
Notation "''PONB'" := ('PONB(_;_)) (only parsing) : type_scope.
Notation "[ 'PONB' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'PONB' 'of' f ]" := (@clone _ _ _ f f _ _ id id) : form_scope.
End Exports.

End PONB.
Export PONB.Exports.

Module ONB.

Section ClassDef.
Variable (H : chsType) (F : finType).

Definition axiom (f : F -> H) := 
  (forall i j, [< f i ; f j >] = (i == j)%:R) /\ #|F| = Vector.dim H.
Definition mixin_of (f : F -> H) := #|F| = Vector.dim H.

Record class_of f : Prop := Class {base : ponbasis f; mixin : mixin_of f}.
Local Coercion base : class_of >-> ponbasis.

Lemma class_of_axiom (f : F -> H) : axiom f -> class_of f.
Proof. by move=>[??]; split. Qed.

Lemma class_of_axiom_split (f : F -> H) :
  (forall i j, [< f i ; f j >] = (i == j)%:R) ->
  #|F| = Vector.dim H -> class_of f.
Proof. by split. Qed.

Structure map (phUV : phant (F -> H)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> H)) (f g : F -> H) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fL of phant_id g (apply cF) & phant_id fL class :=
  @Pack phUV f fL.

Definition pack (fZ : mixin_of f) :=
  fun (bF : PONB.map phUV) fA & phant_id (PONB.class bF) fA =>
  Pack phUV (Class fA fZ).

Definition ponbType := PONB.Pack phUV class.
End ClassDef.

Module Exports.
Notation onbasis f := (axiom f).
Coercion apply : map >-> Funclass.
Coercion class_of_axiom : axiom >-> class_of.
Canonical ponbType.
(* provide orthonormal and card *)
Notation ONBasis fA fB := (Pack (Phant _) (class_of_axiom_split fA fB)).
(* provide card; already a ponbasis *)
Notation CardONBasis fC := (pack fC id).
Notation "''ONB' ( F ; S )" := (map (Phant (F -> S))) : type_scope.
Notation "''ONB[' H ]_ ( F ; S )" := (map (Phant (F -> 'H[H]_S))) : type_scope.
Notation "''ONB_' ( F ; S )" := ('ONB[_]_(F;S)) : type_scope.
Notation "''ONB'" := ('ONB(_;_)) (only parsing) : type_scope.
Notation "[ 'ONB' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'ONB' 'of' f ]" := (@clone _ _ _ f f _ _ id id) : form_scope.
End Exports.

End ONB.
Export ONB.Exports.

Module NormalizedState.

Section ClassDef.
Variable (U : chsType).
Definition axiom (v : U) := [< v ; v >] == 1.
Structure type := Pack { sort: U; _ : axiom sort; }.
Local Coercion sort : type >-> CanonicalHermitianSpace.sort.

Variables (T : U) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom cT') in c.
Definition clone c of phant_id class c := @Pack T c.

Local Canonical subType := Eval hnf in [subType for sort].
Definition eqMixin := Eval hnf in [eqMixin of type by <:].
Local Canonical  eqType  := Eval hnf in EqType type eqMixin.
Definition choiceMixin := [choiceMixin of type by <:].
Local Canonical  choiceType  := Eval hnf in ChoiceType type choiceMixin.

End ClassDef.

Module Import Exports.
Coercion sort : type >-> CanonicalHermitianSpace.sort.
Canonical subType.
Canonical eqType.
Canonical choiceType.
Notation NSType M := (@Pack _ _ M).
Notation "''NS' ( S )" := (@type S) : type_scope.
Notation "''NS'" := ('NS(_)) (only parsing) : type_scope.
Notation "''NS[' H ]_ S" := ('NS('H[H]_S))   (only parsing) : type_scope.
Notation "''NS[' H ]_ ( S )" := ('NS[H]_S)    (only parsing) : type_scope.
Notation "''NS_' S"  := ('NS[_]_S) : type_scope.
Notation "''NS_' ( S )" := ('NS_S) (only parsing) : type_scope.
Notation "[ 'NS' 'of' f 'as' g ]" := (@clone _ f g _ idfun) : form_scope.
Notation "[ 'NS' 'of' f ]" := (@clone _ f _ _ id) : form_scope.
End Exports.

End NormalizedState.
Export NormalizedState.Exports.

(* provide the complement of an ponb basis *)
Section PONBDot.
Variable (H : chsType) (F : finType) (f : 'PONB(F;H)).

Lemma ponb_dot i j : [< f i ; f j >] = (i == j)%:R.
Proof. by case: f=>??. Qed.
Lemma ponb_ns i : [< f i ; f i >] == 1.
Proof. by rewrite ponb_dot eqxx. Qed.
Canonical ponb_nsType i := NSType (ponb_ns i). 

Definition ponb2mx := \matrix_(i < #|F|, j < Vector.dim H) v2r (f (enum_val i)) 0 j.
Lemma ponb2mx_row i : row i ponb2mx = v2r (f (enum_val i)).
Proof. by apply/matrixP=>j k; rewrite !mxE ord1. Qed.
Lemma ponb2mx_rowV i : v2r (f i) = row (enum_rank i) ponb2mx.
Proof. by rewrite ponb2mx_row enum_rankK. Qed.

Lemma ponb2mx_unitary : ponb2mx \is unitarymx.
Proof.
apply/unitarymxP/matrixP=>j k; rewrite mulmx_rowcol -map_trmx -tr_row.
rewrite -map_row -conjmxE !ponb2mx_row -[v2r _]trmxK -trmx_mul mxE -dotp_mulmx.
by rewrite ponb_dot mxE (can_eq enum_valK) eq_sym.
Qed.
Lemma ponb_card : (#|F| <= Vector.dim H)%N.
Proof.
move: ponb2mx_unitary=>/mxrank_unitary P.
by move: (rank_leq_col ponb2mx); rewrite P.
Qed.

Definition ponb_compl (i : 'I_(Vector.dim H - #|F|)) :=
  r2v (row i (dsubmx (schmidt (col_mx ponb2mx (0 : 'M_(Vector.dim H - #|F|,_)))))).

Definition ponb_ext (i : F + 'I_(Vector.dim H - #|F|)%N) :=
  match i with inl j => f j | inr j => ponb_compl j end.

Lemma unitarymxK (T : numClosedFieldType) n m (U : 'M[T]_(n,m)) : 
  U \is unitarymx -> U *m U ^*t = 1%:M.
Proof. by move/unitarymxP. Qed.

Lemma ponb_compl_ponb i j : [< ponb_compl i ; ponb_compl j >] = (i == j)%:R.
Proof.
rewrite dotp_mulmx -[_^*m]trmxK -trmx_mul mxE /ponb_compl !r2vK !row_dsubmx.
rewrite conjmxE map_row tr_row -mulmx_rowcol map_trmx -adjmxE unitarymxK.
by apply/schmidt_unitarymx; rewrite subnKC// ponb_card.
by rewrite mxE (inj_eq (@rshift_inj _ _)) eq_sym.
Qed.
Canonical ponb_compl_ponbasis := PONBasis ponb_compl_ponb.

Lemma ponb_ortho_compl i j : [< f i ; ponb_compl j >] = 0.
Proof.
rewrite dotp_mulmx -[_^*m]trmxK -trmx_mul mxE /ponb_compl !r2vK row_dsubmx.
rewrite ponb2mx_rowV {2}(unitary_ext ponb2mx_unitary) row_usubmx conjmxE map_row tr_row.
rewrite -mulmx_rowcol map_trmx -adjmxE unitarymxK.
by apply/schmidt_unitarymx; rewrite subnKC// ponb_card.
by rewrite mxE eq_rlshift.
Qed.

Lemma ponb_ortho_complV i j : [< ponb_compl i ; f j >] = 0.
Proof. by rewrite -conj_dotp ponb_ortho_compl conjC0. Qed.

Lemma ponb_extE i : ponb_ext (inl i) = f i. Proof. by []. Qed.
Lemma ponb_extCE i : ponb_ext (inr i) = ponb_compl i. Proof. by []. Qed.

Lemma ponb_ext_onb i j : [< ponb_ext i ; ponb_ext j >] = (i == j)%:R.
Proof.
by case: i; case: j=>i j; rewrite /ponb_ext/= ?ponb_compl_ponb 
  ?ponb_dot// ?ponb_ortho_compl ?ponb_ortho_complV.
Qed.
Lemma ponb_ext_card : #|[finType of F + 'I_(Vector.dim H - #|F|)%N]| = Vector.dim H.
Proof. by rewrite card_sum card_ord addnC subnK// ponb_card. Qed.
Canonical ponb_ext_onbasis := ONBasis (ponb_ext_onb) ponb_ext_card.

End PONBDot.

Section ONBTheory.
Variable (H : chsType) (F : finType) (f : 'ONB(F;H)).

Lemma onb_dot i j : [< f i ; f j >] = (i == j)%:R. Proof. exact: ponb_dot. Qed.

Lemma onb_card : #|F| = Vector.dim H.
Proof. by case: f=>?[??]. Qed.

Local Notation "'''' i" := (cast_ord onb_card (enum_rank i)) (at level 2).
Definition onb2eb : 'End(H) := \sum_i [> eb ''i ; f i <].
Definition eb2onb : 'End(H) := \sum_i [> f i ; eb ''i <].

Lemma onb2eb_adj : onb2eb^A = eb2onb.
Proof. by rewrite /onb2eb /eb2onb raddf_sum/=; under eq_bigr do rewrite adj_outp. Qed.
Lemma eb2onb_adj : eb2onb^A = onb2eb.
Proof. by rewrite -onb2eb_adj adjfK. Qed.

Lemma onb2eb_unitary : onb2eb \is unitarylf.
Proof.
apply/unitarylfPV; rewrite onb2eb_adj /onb2eb /eb2onb linear_sumr/=.
rewrite [LHS](eq_bigr (fun i=>[> eb ''i; eb ''i <])).
by move=>i _; rewrite linear_suml/= (bigD1 i)//= big1=>[j/negPf nj|];
rewrite outp_comp onb_dot ?nj ?scale0r// eqxx scale1r addr0.
symmetry; rewrite -sumeb_out; apply: reindex; apply bij_ord_enum.
Qed.

Lemma sumonb_out : \sum_i [> f i ; f i <] = \1.
Proof.
move: onb2eb_unitary=>/unitarylfP<-. symmetry.
rewrite onb2eb_adj /eb2onb /onb2eb linear_sumr/=; apply eq_bigr=>i _.
rewrite (bigD1 i)//= comp_lfunDl linear_suml big1/==>[j/negPf nj|];
by rewrite outp_comp cbase -enum_ord_eq cast_ord_comp cast_ord_id enum_rankK 
  ?nj ?scale0r// eqxx scale1r addr0.
Qed.

Lemma onb_vec (v : H) : v = \sum_i [< f i ; v >] *: f i.
Proof. by under eq_bigr do rewrite -outpE; rewrite -sum_lfunE sumonb_out lfunE. Qed.

Lemma outp_complV (G : chsType) (u v : H) (g : 'Hom(H,G)) :
  [> g u ; v <] = g \o [> u ; v <].
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE linearZ/=. Qed.

Lemma outp_comprV (G : chsType) (u v : H) (g : 'Hom(H,G)) :
  [> u ; g v <] = [> u ; v <] \o g^A.
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE adj_dotEV. Qed.

Lemma onb_lfun (G : chsType) (g : 'Hom(H,G)) : g = \sum_i [> g (f i) ; f i <].
Proof. 
under eq_bigr do rewrite outp_complV.
by rewrite -linear_sumr/= sumonb_out comp_lfun1r.
Qed.

Lemma intro_onbl (u v: H) : 
  (forall i, [< f i ; u >] = [< f i ; v >]) <-> u = v.
Proof.
split=>[P|->//]; apply intro_dotl=> t; rewrite (onb_vec t) !dotp_suml.
by apply eq_bigr=>i _; rewrite !dotpZl P.
Qed.

Lemma intro_onbr (u v: H) : 
  (forall i, [< u ; f i >] = [< v ; f i >]) <-> u = v.
Proof.
split=>[|->//]; rewrite -intro_onbl=> P t.
by apply (can_inj conjCK); rewrite !conj_dotp.
Qed.

Lemma onb_trlf x : \Tr x = \sum_i [< f i ; x (f i) >].
Proof. 
rewrite {1}(onb_lfun x) linear_sum/=; apply eq_bigr=>i _.
by rewrite outp_trlf.
Qed.

Lemma intro_onb (G : chsType) (g h : 'Hom(H,G)) :
  (forall i, g (f i) = h (f i)) <-> g = h.
Proof.
split=>[P|->//]; apply/lfunP=>u; rewrite (onb_vec u) !linear_sum/=.
by apply eq_bigr=>i _; rewrite !linearZ/= P.
Qed.

End ONBTheory.

Section ONB2Theory.
Variable (U V : chsType) (F G : finType) (ou : 'ONB(F;U)) (ov : 'ONB(G;V)).

Lemma onb_lfun2 (E : 'Hom(U,V)) : 
  E = \sum_i \sum_j [< ov j ; E (ou i) >] *: [> ov j ; ou i <].
Proof.
rewrite [LHS](onb_lfun ou); apply eq_bigr=>i _.
by rewrite {1}(onb_vec ov (E (ou i))) linear_suml/=; under eq_bigr do rewrite linearZl.
Qed.

Lemma onb_lfun2id (E : 'End(U)) : 
  E = \sum_i \sum_j [< ou j ; E (ou i) >] *: [> ou j ; ou i <].
Proof.
rewrite [LHS](onb_lfun ou); apply eq_bigr=>i _.
by rewrite {1}(onb_vec ou (E (ou i))) linear_suml/=; under eq_bigr do rewrite linearZl.
Qed.

End ONB2Theory.

Section DefaultONB.

Lemma eb_card (H : chsType) : #|'I_(Vector.dim H)| = Vector.dim H.
Proof. by rewrite card_ord. Qed.

Canonical eb_ponbasis (H : chsType) := 
  PONBasis (@cbase H) : 'PONB('I_(Vector.dim H); H).
Canonical eb_onbasis (H : chsType) := 
  ONBasis (@cbase H) (@eb_card H) : 'ONB('I_(Vector.dim H); H).

Lemma idx_card (L : finType) (H : L -> chsType) (S : {set L}) :
  #|[finType of 'Idx[H]_S]| = Vector.dim 'H[H]_S.
Proof.
rewrite card_mv/= card_dep_ffun dim_setten foldrE big_image/=.
by rewrite (eq_bigr (fun j=> (locked_with tt (fun x : L=> Vector.dim (H x))) (val j)))
  =>[i Pi|]; rewrite ?big_sig_set// card_ord.
Qed.

Canonical deltav_ponbasis (L : finType) (H : L -> chsType) (S : {set L}) := 
  PONBasis (@tcbase L H S) : 'PONB('Idx[H]_S; 'H[H]_S).
Canonical deltav_onbasis (L : finType) (H : L -> chsType) (S : {set L}) := 
  ONBasis (@tcbase L H S) (@idx_card L H S) : 'ONB('Idx[H]_S; 'H[H]_S).

End DefaultONB.

Arguments eb_onbasis {H}.
Arguments deltav_onbasis {L H S}.

Section NormalizedStateTheory.
Implicit Types (U V : chsType).

Lemma ns_dot U (v : 'NS(U)) : [<v : U ; v : U>] = 1.
Proof. by destruct v; apply/eqP. Qed.

Lemma ns_norm U (v : 'NS(U)) : `|v : U| = 1.
Proof. by rewrite hnormE ns_dot sqrtC1. Qed.

Lemma ns_neq0 U (v : 'NS(U)) : (v : U) != 0.
Proof. by rewrite -normr_eq0 ns_norm oner_neq0. Qed.

Lemma ns_eq0 U (v : 'NS(U)) : (v : U) == 0 = false.
Proof. by apply/eqP/eqP; exact: ns_neq0. Qed.

Lemma ns_scale_eq0 U (v : 'NS(U)) (c : C) : c *: (v : U) == 0 = (c == 0).
Proof. by rewrite scaler_eq0 ns_eq0 orbF. Qed.

Lemma ns_scaleI U (v : 'NS(U)) (c c' : C) : 
  c *: (v : U) = c' *: (v : U) -> (c = c').
Proof. by move=>/eqP; rewrite -subr_eq0 -scalerBl ns_scale_eq0 subr_eq0=>/eqP. Qed.

Lemma eb_ns_subproof U (i : 'I_(Vector.dim U)) : [<eb i; eb i>] == 1.
Proof. by rewrite cbase eqxx. Qed.
Canonical eb_nsType U i := NSType (@eb_ns_subproof U i).

Lemma onb_ns_subproof U (F : finType) (f : 'ONB(F;U)) i :
  [<f i ; f i>] == 1.
Proof. by rewrite onb_dot eqxx. Qed.
Canonical onb_nsType U F f i := NSType (@onb_ns_subproof U F f i).

Canonical deltav_nsType (L : finType) (H : L -> chsType) (S : {set L}) 
  (i : 'Idx[H]_S) := Eval hnf in [NS of deltav i].

End NormalizedStateTheory.

Section LownerorderLfun.
Context {V: chsType}.
Implicit Type (f g h : 'End(V)).

Definition lef_def f g := (g - f) \is psdlf.
Definition ltf_def f g := (g != f) && (lef_def f g).

Lemma lef_def_mx f g : lef_def f g = (f2mx f ⊑ f2mx g).
Proof. by rewrite /lef_def qualifE linearB/= le_lownerE. Qed.

Lemma ltf_def_mx f g : ltf_def f g = (f2mx f ⊏ f2mx g).
Proof. by rewrite /ltf_def lt_def (can_eq (@f2mxK _ _ _)) lef_def_mx. Qed.

Lemma ltf_def_def : forall f g, ltf_def f g = (g != f) && (lef_def f g).
Proof. by rewrite /lef_def. Qed.

Lemma lef_def_anti : antisymmetric lef_def.
Proof. by move=>x y; rewrite !lef_def_mx -eq_le=>/eqP/f2mx_inj. Qed.

Lemma lef_def_refl : reflexive lef_def.
Proof. by move=>x; rewrite lef_def_mx. Qed.

Lemma lef_def_trans : transitive lef_def.
Proof. by move=>x y z; rewrite !lef_def_mx; apply le_trans. Qed.

Definition lownerlf_porderMixin := LePOrderMixin 
ltf_def_def lef_def_refl lef_def_anti lef_def_trans.

Canonical lownerlf_porderType := POrderType vorder_display 'End(V) lownerlf_porderMixin.

Definition denlf_lporderMixin := [porderMixin of 'FD(V) by <:].
Canonical denlf_lporderType :=
  Eval hnf in POrderType vorder_display 'FD(V) denlf_lporderMixin.

Definition obslf_lporderMixin := [porderMixin of 'FO(V) by <:].
Canonical denmx_lporderType :=
  Eval hnf in POrderType vorder_display 'FO(V) obslf_lporderMixin.

Lemma lef_mx f g : f ⊑ g = (f2mx f ⊑ f2mx g).
Proof. by rewrite {1}/Order.le/= lef_def_mx. Qed.

Lemma ltf_mx f g : f ⊏ g = (f2mx f ⊏ f2mx g).
Proof. by rewrite {1}/Order.lt/= ltf_def_mx. Qed.

Lemma lef_add2rP h f g : f ⊑ g -> (f + h) ⊑ (g + h).
Proof. by rewrite addrC /Order.le/= /lef_def opprD addrA addrK. Qed.

Lemma lef_pscale2lP (e : C) f g : 0 < e -> f ⊑ g -> (e *: f) ⊑ (e *: g).
Proof. rewrite !lef_mx !linearZ/=; exact: lev_pscale2lP. Qed.

Lemma pscalef_lge0 f (a : C) : 
  (0 : 'End(V)) ⊏ f -> (0 : 'End(V)) ⊑ a *: f = (0 <= a).
Proof. rewrite lef_mx ltf_mx linear0 linearZ/=; exact: pscalev_lge0. Qed.

Import VOrder.Exports.
Definition lownerlf_vorderMixin := VOrderMixin lef_add2rP lef_pscale2lP.
Canonical lownerlf_vorderType := VOrderType C 'End(V) lownerlf_vorderMixin.

Import CanVOrder.Exports.
Definition lownerlf_canVOrderMixin := CanVOrderMixin pscalef_lge0.
Canonical lownerlf_canVOrderType := CanVOrderType C 'End(V) lownerlf_canVOrderMixin.

Lemma lefE f g : f ⊑ g = (g - f \is psdlf).
Proof. by rewrite {1}/Order.le/=. Qed.

Lemma lef_dot f g : f ⊑ g <-> forall v, [<v ; f v>] <= [<v ; g v >].
Proof.
rewrite {1}/Order.le [in X in X <-> _]/= /lef_def. 
split=>[/psdlfP P v|P]; last apply/psdlfP=>v.
all: by move: (P v); rewrite !lfunE/= !lfunE/= linearB/= subr_ge0.
Qed.

Local Notation "0" := (0 : 'End(V)).

(* Properties of the psdlf subset. *)
Lemma psdlfE f : (f \is psdlf) = (0 ⊑ f). Proof. by rewrite lefE subr0. Qed.
Lemma psdlf_ge0 f : f \is psdlf -> 0 ⊑ f. Proof. by rewrite psdlfE. Qed.
Lemma psdf_ge0 (f : 'F+(V)) : 0 ⊑ f. Proof. apply/psdlf_ge0/psdf_psd. Qed.
Lemma gef0_psd f : 0 ⊑ f -> f \is psdlf.  Proof. by rewrite psdlfE => ->. Qed.
Lemma gtf0_psd f : 0 ⊏ f -> f \is psdlf.  Proof. by move=> /ltW/gef0_psd. Qed.
Hint Resolve psdlf0 : core.
Hint Resolve psdlf1 : core.

Lemma psdf_le0 (f : 'F+(V)) : f%:VF ⊑ 0 -> f = 0 :> 'End(V).
Proof. by move=>P; apply/le_anti; rewrite P psdf_ge0. Qed.

Lemma psdlfD : {in psdlf &, forall f g, f + g \is psdlf}.
Proof. by move=>f g; rewrite !psdlfE; exact: addv_ge0. Qed.
Lemma psdfD (A B : 'F+(V)) : A%:VF + B \is psdlf.
Proof. apply/psdlfD; apply/psdf_psd. Qed.
Canonical add_psdfType A B := PsdfType (psdfD A B).

Lemma ge0_form f : 0 ⊑ f -> exists g, f = g^A \o g.
Proof.
rewrite -psdlfE qualifE=>/psdmx_form[B PB].
exists (Vector.Hom B). apply/f2mx_inj; by rewrite f2mx_comp/=.
Qed.

Lemma ge0_formV f : 0 ⊑ f -> exists g, f = g \o g^A.
Proof. by move=>/ge0_form[g Pg]; exists g^A; rewrite adjfK. Qed.

Lemma gtf0_pd f : reflect (0 ⊑ f /\ exists v, [<v ; f v>] != 0%R) (0 ⊏ f).
Proof.
rewrite lt_def; apply/(iffP andP); move=>[P1 P2]; split=>//.
move: P1=>/eqP; rewrite not_existsP; apply contra_not=>P1.
move: P2=>/ge0_form[g Pg]; apply/lfunP=>v; move: (P1 v)=>/negP. 
rewrite negbK Pg lfunE/= adj_dotE adjfK dotp_eq0=>/eqP->.
by rewrite !lfunE/= linear0.
by move: P2=>[v]; apply contraNN=>/eqP->; rewrite lfunE/= linear0.
Qed.

Lemma gtf0_pdP f : reflect (0 ⊑ f /\ exists v, 0%:R < [<v ; f v>]) (0 ⊏ f).
Proof.
apply/(iffP (gtf0_pd f)); move=>[fge0 [v Pv]]; split=>//; exists v.
by rewrite lt0r Pv/=; apply/psdlfP; rewrite psdlfE.
by apply/lt0r_neq0.
Qed.

Lemma lef01 : 0 ⊑ \1.
Proof. by apply lef_dot=>v; rewrite !lfunE/= linear0 ge0_dotp. Qed.

Lemma ltf01 : 0 ⊏ \1.
Proof. by rewrite lt_def lef01 oner_neq0. Qed.

(* Comparision and opposite. *)
Local Notation "-%R" := (@GRing.opp [lmodType C of 'End(V)]).

Lemma lef_adj x y : (x^A ⊑ y^A) = (x ⊑ y).
Proof. by rewrite -subv_ge0 -psdlfE -linearB/= psdlf_adj psdlfE subv_ge0. Qed.
Lemma lef_conj x y : (x^C ⊑ y^C) = (x ⊑ y).
Proof. by rewrite -subv_ge0 -psdlfE -linearB/= psdlf_conj psdlfE subv_ge0. Qed.
Lemma lef_tr x y : (x^T ⊑ y^T) = (x ⊑ y).
Proof. by rewrite !trfAC lef_conj lef_adj. Qed.

Lemma lef_trlf f g : f ⊑ g -> \Tr f <= \Tr g.
Proof. by rewrite lefE=>/psdlf_trlf; rewrite linearB/= subr_ge0. Qed.

Lemma lef_dentr f g :
  reflect (forall x, x \is denlf -> \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
rewrite lef_mx; apply/(iffP (@le_lownerE_dentr _ _ _))=>P x Px.
rewrite /lftrace !f2mx_comp ![\tr (f2mx x *m _)]mxtrace_mulC P=>[|//].
by move: Px; rewrite qualifE.
have: Vector.Hom x \is denlf by rewrite qualifE.
by move=>/P; rewrite /lftrace !f2mx_comp/= ![\tr (x *m _)]mxtrace_mulC.
Qed.

Lemma lef_psdtr f g :
  reflect (forall x, x \is psdlf -> \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
apply/(iffP idP)=>[|P]; last by apply/lef_dentr=>x /denlf_psd/P.
rewrite lef_mx=>/le_lownerE_psdtr P x; rewrite qualifE=>/P.
by rewrite /lftrace !f2mx_comp ![\tr (f2mx x *m _)]mxtrace_mulC.
Qed.

Lemma lef_obstr f g : 
  reflect (forall x, x \is obslf -> \Tr (f \o x) <= \Tr (g \o x))	(f ⊑ g).
Proof.
apply/(iffP idP)=>[/lef_psdtr P x /obslf_psd/P//|P].
by apply/lef_dentr=>x /denlf_obs/P.
Qed.

Lemma lef_trden f g : 
  reflect (forall x : 'FD(V), \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
apply/(iffP (lef_dentr _ _))=>[H x|H x P].
by apply H; destruct x. by move: (H (DenfType P)).
Qed.

Lemma lef_trobs f g : 
  reflect (forall x : 'FO(V), \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
apply/(iffP (lef_obstr _ _))=>[H x|H x P].
by apply H; destruct x. by move: (H (ObsfType P)).
Qed.

End LownerorderLfun.

Section LownerorderForm.
Variable (U V: chsType) .

Lemma formV_ge0 (f : 'Hom(U,V)) :  (0 : 'End(V)) ⊑ f \o f^A.
Proof. by rewrite -psdlfE; apply/psdlfP=>v; rewrite lfunE/= adj_dotE ge0_dotp. Qed.

Lemma form_ge0 (f : 'Hom(U,V)) : (0 : 'End(U)) ⊑ f^A \o f.
Proof. by rewrite -psdlfE; apply/psdlfP=>v; rewrite lfunE/= adj_dotE adjfK ge0_dotp. Qed.

Lemma form_eq0 (f : 'Hom(U,V)) : f^A \o f == 0 = (f == 0).
Proof.
apply/eqb_iff; rewrite !eq_iff; split=>[P1|->]; last by rewrite comp_lfun0r.
apply/lfunP=>v; rewrite lfunE/=; apply/eqP;
by rewrite -normr_eq0 hnormE adj_dotE -comp_lfunE P1 lfunE/= linear0l sqrtC0.
Qed.

Lemma formV_eq0 (f : 'Hom(U,V)) : f \o f^A == 0 = (f == 0).
Proof. 
apply/eqb_iff; rewrite !eq_iff; split=>[P1|->]; last by rewrite comp_lfun0l.
apply/adjf_inj/lfunP=>v; rewrite raddf0 lfunE/=; apply/eqP;
by rewrite -normr_eq0 hnormE -adj_dotE -comp_lfunE P1 lfunE/= linear0 sqrtC0.
Qed.

Lemma lef_formV (g1 g2: 'End(U)) (f: 'Hom(U,V))  :
  g1 ⊑ g2 -> f \o g1 \o f^A ⊑ f \o g2 \o f^A.
Proof.
move=>/lef_dot=>P; apply/lef_dot=>v; move: (P (f^A v)).
by rewrite !lfunE/= !lfunE/= -!adj_dotE.
Qed.

Lemma lef_form (g1 g2: 'End(U)) (f: 'Hom(V,U)) :
  g1 ⊑ g2 -> f^A \o g1 \o f ⊑ f^A \o g2 \o f.
Proof. by move=>/(@lef_formV _ _ f^A); by rewrite !adjfK. Qed.

Lemma gef0_formV (g: 'End(U)) (f: 'Hom(U,V))  :
  (0 : 'End(_)) ⊑ g -> (0 : 'End(_)) ⊑ f \o g \o f^A.
Proof. by move=>/(lef_formV f); rewrite comp_lfun0r comp_lfun0l. Qed.

Lemma gef0_form (g: 'End(U)) (f: 'Hom(V,U))  :
  (0 : 'End(_)) ⊑ g -> (0 : 'End(_)) ⊑ f^A \o g \o f.
Proof. by move=>/(lef_form f); rewrite comp_lfun0r comp_lfun0l. Qed.

End LownerorderForm.

Section LownerorderExtra.
Variable (U: chsType).

Lemma lef_obs (f: 'End(U)) :
  f \is obslf = (((0 : 'End(U)) ⊑ f) && (f ⊑ \1)).
Proof. by rewrite !lef_mx qualifE obsmx_psd_eq !le_lownerE f2mx1 linear0 subr0. Qed.

Lemma psdlf_TrM (f g: 'End(U)) : 
  f \is psdlf -> g \is psdlf -> 0%:R <= \Tr (f \o g).
Proof.
rewrite !psdlfE=>/ge0_form[h ->] /(lef_formV h)/lef_trlf.
by rewrite comp_lfun0r comp_lfun0l linear0 [\Tr (_ \o h^A)]lftraceC comp_lfunA.
Qed.

Lemma denf_ges0 (x : 'FD(U)) : [den of 0] ⊑ x.
Proof. by rewrite leEsub/= -psdlfE; apply/denlf_psd/denf_den. Qed.

Lemma denf_ge0 (x : 'FD(U)) : (0 : 'End(U)) ⊑ x.
Proof. by move: (denf_ges0 x); rewrite leEsub. Qed.

Lemma denf_le1 (x : 'FD(U)) : (x : 'End(U)) ⊑ (\1 : 'End(U))%VF.
Proof.
destruct x=>/=. move: i=>/denlf_obs/obslfP[_ P]. 
rewrite lefE. apply/psdlfP=>u. do ? rewrite !lfunE/=.
by rewrite linearB/= subr_ge0 P.
Qed.

Lemma obsf_ges0 (x : 'FO(U)) : [obs of 0] ⊑ x.
Proof. by rewrite leEsub/= -psdlfE; apply/obslf_psd/obsf_obs. Qed.

Lemma obsf_ge0 (x : 'FO(U)) : (0 : 'End(U)) ⊑ x.
Proof. by move: (obsf_ges0 x); rewrite leEsub. Qed.

Lemma obsf_les1 (x : 'FO(U)) : x ⊑ [obs of \1].
Proof.
rewrite leEsub/= lefE; move: (obsf_obs x)=>/obslfP[_ P].
by apply/psdlfP=>u; rewrite lfunE/= !lfunE/= linearB/= subr_ge0 P.
Qed.

Lemma obslf_le1 (x : 'End(U)) : x \is obslf -> x ⊑ \1.
Proof. by move=>P; move: (obsf_les1 (ObsfType P)); rewrite leEsub. Qed.

Lemma obsf_le1 (x : 'FO(U)) : (x : 'End(U)) ⊑ \1.
Proof. apply/obslf_le1/obsf_obs. Qed.

Lemma obslfE (A : 'End(U)) : A \is obslf = ((0%:VF ⊑ A) && (A ⊑ \1)).
Proof.
apply/eqb_iff; split=>[P1|/andP[P1 P2]].
by rewrite -(obsfE tt P1) psdf_ge0 obsf_le1.
apply/obslfP; split=>[|u]; rewrite ?psdlfE// -subr_ge0 -linearB/= -{2}(id_lfunE u).
by rewrite -opp_lfunE -add_lfunE; apply/psdlfP; rewrite psdlfE subv_ge0.
Qed.
Lemma obslf_lefP (A : 'End(U)) : 
  reflect (0%:VF ⊑ A /\ (A ⊑ \1)) (A \is obslf).
Proof. by rewrite obslfE; apply/(iffP andP). Qed.

End LownerorderExtra.

Section LownerorderTensorLfun.
Context {L: finType} (H: L -> chsType).
Implicit Type (S T : {set L}).

Lemma trlf_deltavl S T (f : 'F[H]_S) (g : 'F_T) (i j : 'Idx[H]_(S :|: T)) :
  \Tr ([>deltav i ; deltav j <] \o (f \⊗ g)) = 
  \Tr ([>deltav (idxSl i) ; deltav (idxSl j) <] \o f) *
  \Tr ([>deltav (idxSr i) ; deltav (idxSr j) <] \o g).
Proof. by rewrite !outp_compl !outp_trlf -!adj_dotE -tenfdv -!cdvE cdvt. Qed.

Lemma trlf_introdvr S T (f1 f2: 'F[H]_(S,T)) :
  (forall i j, \Tr (f1 \o [>deltav i ; deltav j <]) = \Tr (f2 \o [>deltav i ; deltav j <])) 
  <-> (f1 = f2).
Proof.
split=>[P|->//]; apply/lfunPD=>i; apply/cdvP=>j. 
by rewrite !cdvE -!outp_trlf -!outp_compr P.
Qed.

Lemma trlf_introdvl S T (f1 f2: 'F[H]_(S,T)) :
  (forall i j, \Tr ([>deltav i ; deltav j <] \o f1) = \Tr ([>deltav i ; deltav j <] \o f2)) 
  <-> (f1 = f2).
Proof.
rewrite -trlf_introdvr; split=>P i j; move: (P i j);
by rewrite ![\Tr (outp _ _ \o _)]lftraceC.
Qed.

Lemma castlf_trlf S S' (eqS : S = S') (x : 'F[H]_S) :
  \Tr x = \Tr (castlf (eqS,eqS) x).
Proof. by case: S' / eqS; rewrite castlf_id. Qed.

Lemma lef_cast S S' (eqS : S = S') (f g : 'F[H]_S) :
  castlf (eqS,eqS) f ⊑ castlf (eqS,eqS) g = (f ⊑ g).
Proof. by case: S' / eqS; rewrite !castlf_id. Qed.

Lemma lef_cast_sym S S' (eqS : S = S') (f : 'F[H]_S) (g : 'F[H]_S'):
  castlf (eqS,eqS) f ⊑ g = (f ⊑ castlf (esym eqS, esym eqS) g).
Proof. by case: S' / eqS g; rewrite !castlf_id. Qed.

Lemma lef_cast_symV S S' (eqS : S' = S) (f : 'F[H]_S) (g : 'F[H]_S'):
  f ⊑ castlf (eqS,eqS) g = (castlf (esym eqS, esym eqS) f ⊑ g).
Proof. by case: S / eqS f; rewrite !castlf_id. Qed.

Lemma ltf_cast S S' (eqS : S = S') (f g : 'F[H]_S) :
  castlf (eqS,eqS) f ⊏ castlf (eqS,eqS) g = (f ⊏ g).
Proof. by case: S' / eqS; rewrite !castlf_id. Qed.

Lemma ltf_cast_sym S S' (eqS : S = S') (f : 'F[H]_S) (g : 'F[H]_S'):
  castlf (eqS,eqS) f ⊏ g = (f ⊏ castlf (esym eqS, esym eqS) g).
Proof. by case: S' / eqS g; rewrite !castlf_id. Qed.

Lemma ltf_cast_symV S S' (eqS : S' = S) (f : 'F[H]_S) (g : 'F[H]_S'):
  f ⊏ castlf (eqS,eqS) g = (castlf (esym eqS, esym eqS) f ⊏ g).
Proof. by case: S / eqS f; rewrite !castlf_id. Qed.

Lemma castlf_le1 S S' (eqS: S = S') (f : 'F[H]_S) : 
  castlf (eqS,eqS) f ⊑ \1 = (f ⊑ \1).
Proof. by case: S' / eqS; rewrite castlf_id. Qed.

Lemma castlf_ge0 S S' (eqS: S = S') (f : 'F[H]_S) : 
  (0 : 'F[H]_S') ⊑ castlf (eqS,eqS) f = ((0 : 'F[H]_S)  ⊑ f).
Proof. by case: S' / eqS; rewrite castlf_id. Qed.

Lemma tenf_ge0 S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] -> (0 :'F[H]_S) ⊑ f -> (0 :'F[H]_T) ⊑ g -> (0 :'F[H]_(S :|: T)) ⊑ f \⊗ g.
Proof.
move=>P1 /ge0_form[f1 Pf] /ge0_form[g1 Pg].
by rewrite Pf Pg tenf_comp// -tenf_adj form_ge0.
Qed.

Lemma lfun_neq0P (U V : chsType) (f : 'Hom(U,V)) : 
  reflect (exists v, [< f v ; f v >] != 0) (f != 0).
Proof.
apply/(iffP negP); rewrite not_existsP; apply contra_not.
by move=>P; apply/eqP/lfunP=>u; move: (P u)=>/negP; rewrite negbK dotp_eq0 lfunE/==>/eqP.
by move=>/eqP-> x; rewrite lfunE/= linear0 eqxx.
Qed.

Lemma tenf_eq0 S T (dis : [disjoint S & T]) (f : 'F[H]_S) (g : 'F[H]_T) :
  f \⊗ g == 0 = (f == 0) || (g == 0).
Proof.
apply/Bool.eq_iff_eq_true; split.
move=>/eqP/lfunP P1. case: eqP=>//=; move=>/eqP/lfun_neq0P[v /negPf Pv].
apply/eqP/lfunP=>x; apply/intro_dotl=>y; 
move: (P1 (tenv v x))=>/intro_dotl/(_ (tenv (f v) y))/eqP.
by rewrite tenf_apply// tenv_dot// !lfunE/= !linear0 mulf_eq0 Pv/==>/eqP.
by move=>/orP[/eqP->|/eqP->]; rewrite ?linear0l ?linear0r eqxx.
Qed.

Lemma ptenf_rge0 S T (dis : [disjoint S & T]) (x : 'F[H]_S) (y : 'F[H]_T) :
  (0 : 'F__) ⊏ x -> ((0 : 'F__) ⊑ x \⊗ y) = ((0 : 'F__) ⊑ y).
Proof.
move=>/gtf0_pdP[xge0 [v Pv]].
apply/Bool.eq_iff_eq_true; split; last by apply: tenf_ge0=>//.
move/lef_dot=>P1. apply/lef_dot=>u.
move: (P1 (tenv v u)).
by rewrite !tenf_apply// tenv_dot// !lfunE/= !linear0 pmulr_rge0.
Qed.

Lemma ptenf_lge0 S T (dis : [disjoint S & T]) (y : 'F[H]_T) (x : 'F[H]_S) :
  (0 : 'F__) ⊏ y -> ((0 : 'F__) ⊑ x \⊗ y) = ((0 : 'F__) ⊑ x).
Proof.
by move=>Q; rewrite -tenf_castC lef_cast_symV linear0 ptenf_rge0// disjoint_sym.
Qed.

Definition tenf_bregVOrderMixin S T dis := 
    bregVOrderMixin (@tenf_eq0 S T dis) (ptenf_rge0 dis) (ptenf_lge0 dis).
Canonical tenf_bregVOrderType S T dis := 
  bregVOrderType (@ten_lfun _ _ S S T T) (@tenf_bregVOrderMixin S T dis).

Lemma ptenf_rgt0 S T (dis : [disjoint S & T]) (x : 'F[H]_S) (y : 'F[H]_T) :
  (0 : 'F__) ⊏ x -> ((0 : 'F__) ⊏ x \⊗ y) = ((0 : 'F__) ⊏ y).
Proof. exact: pbregv_rgt0. Qed.

Lemma ptenf_lgt0 S T (dis : [disjoint S & T]) (y : 'F[H]_T) (x : 'F[H]_S) :
  (0 : 'F__) ⊏ y -> ((0 : 'F__) ⊏ x \⊗ y) = ((0 : 'F__) ⊏ x).
Proof. exact: pbregv_lgt0. Qed.

(* if needed, add similar things in mxcvg : vorder scale *)
Lemma lef_tenfl S T (dis : [disjoint S & T]) (f1 f2: 'F[H]_S) (g: 'F[H]_T) :
  (0 :'F[H]_T) ⊑ g -> f1 ⊑ f2 -> f1 \⊗ g ⊑ f2 \⊗ g.
Proof. move=>p1; exact: (lev_wpbreg2r _ p1). Qed.

Lemma lef_tenfr S T (dis : [disjoint S & T]) (g: 'F[H]_S) (f1 f2: 'F[H]_T) :
  (0 :'F[H]_S) ⊑ g -> f1 ⊑ f2 -> g \⊗ f1 ⊑ g \⊗ f2.
Proof. by move=>p1; apply: (lev_wpbreg2l _ p1). Qed.

End LownerorderTensorLfun.

Section SuperOperator.
Variable (U V: chsType).

Variant superop : predArgType := 
  Superop of 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)]).

Definition so_val A := let: Superop g := A in g.

Canonical superop_subType := Eval hnf in [newType for so_val].

Fact superop_key : unit. Proof. by []. Qed.
Definition superop_of_fun_def F := Superop F.
Definition superof_of_fun k := locked_with k superop_of_fun_def.
Canonical superof_unlockable k := [unlockable fun superof_of_fun k].

Definition fun_of_superof A x := so_val A x.

Coercion fun_of_superof : superop >-> Funclass.

Lemma superopE k F : superof_of_fun k F =1 F.
Proof. by move=> i; rewrite unlock /fun_of_superof. Qed.

Lemma soK k F : so_val (superof_of_fun k F) = F.
Proof. by rewrite unlock/=. Qed.

Lemma superopP (A B : superop) : A =1 B <-> A = B.
Proof.
rewrite /fun_of_superof; split=> [/= eqAB | -> //].
by apply/val_inj/lfunP=>i; apply eqAB.
Qed.

Lemma superop_is_linear (A: superop) : linear A.
Proof. by move=>a x y; rewrite /fun_of_superof/= linearP. Qed.
Canonical superop_linear (A: superop) := Linear (@superop_is_linear A).

Lemma so_psdP (u v : superop) : (forall x, x \is psdlf -> u x = v x) <-> u = v.
Proof.
split=>[P|->//]. apply/superopP=>x.
move: (lf_psd_decomp x)=>[f1 [f2 [f3 [f4]]]] [/P P1] [/P P2] [/P P3] [/P P4]->.
by rewrite !linearD/= !linearN/= !linearZ/= P1 P2 P3 P4.
Qed.

Lemma so_ebP (u v : superop) : (forall i j, u (delta_lf i j) = v (delta_lf i j)) <-> u = v.
Proof.
split=>[P|->//]; apply/superopP=>x.
rewrite (lfun_sum_delta x) !linear_sum/=. apply eq_bigr=>i _.
rewrite !linear_sum/=. apply eq_bigr=>j _. by rewrite !linearZ/= P.
Qed.

Lemma eq_so k (F1 F2 : 'Hom([vectType C of 'End(U)], [vectType C of 'End(V)])) : 
  (F1 =1 F2) -> superof_of_fun k F1 = superof_of_fun k F2.
Proof. by move=> eq_F; apply/superopP => i; rewrite !superopE eq_F. Qed.

Definition superop_eqMixin := Eval hnf in [eqMixin of superop by <:].
Canonical superop_eqType := Eval hnf in EqType superop superop_eqMixin.
Definition superop_choiceMixin := [choiceMixin of superop by <:].
Canonical superop_choiceType := 
  Eval hnf in ChoiceType superop superop_choiceMixin.

Definition abortso := superof_of_fun superop_key 0.
Definition oppso A := superof_of_fun superop_key (- (so_val A)).
Definition addso A B := superof_of_fun superop_key ((so_val A) + (so_val B)).
Definition scaleso x A := superof_of_fun superop_key (x *: (so_val A)).
Lemma addsoA : associative addso.
Proof. by move=> A B C; apply/val_inj; rewrite /= !soK addrA. Qed.
Lemma addsoC : commutative addso.
Proof. by move=> A B; apply/val_inj; rewrite /= !soK addrC. Qed.
Lemma add0so : left_id abortso addso.
Proof. by move=> A; apply/val_inj; rewrite /= !soK add0r. Qed.
Lemma addNso : left_inverse abortso oppso addso.
Proof. by move=> A; apply/val_inj; rewrite /= !soK addNr. Qed.

Definition superop_zmodMixin := ZmodMixin addsoA addsoC add0so addNso.
Canonical superop_zmodType := Eval hnf in ZmodType superop superop_zmodMixin.

Lemma scale1so A : scaleso 1 A = A.
Proof. by apply/val_inj; rewrite /= !soK scale1r. Qed.
Lemma scalesoDl A (x y : C) : scaleso (x + y) A = scaleso x A + scaleso y A.
Proof. by apply/val_inj; rewrite /= !soK scalerDl. Qed.
Lemma scalesoDr (x : C) A B : scaleso x (A + B) = scaleso x A + scaleso x B.
Proof. by apply/val_inj; rewrite /= !soK scalerDr. Qed.
Lemma scalesoA (x y : C) A : scaleso x (scaleso y A) = scaleso (x * y) A.
Proof. by apply/val_inj; rewrite /= !soK scalerA. Qed.

Definition superop_lmodMixin := LmodMixin scalesoA scale1so scalesoDr scalesoDl.
Canonical superop_lmodType := Eval hnf in LmodType C superop superop_lmodMixin.
Lemma soconstruct_is_linear : linear Superop.
Proof. by move=>x A B; apply/val_inj; rewrite /=!soK. Qed.
Canonical soconstruct_linear := Linear soconstruct_is_linear.
Lemma so_val_is_linear : linear so_val.
Proof. by move=>x A B; rewrite !soK. Qed.
Canonical so_val_linear := Linear so_val_is_linear.

Lemma abort_soE x : abortso x = 0. Proof. by rewrite superopE lfunE. Qed.
Lemma add_soE (f g : superop) x : (f + g) x = f x + g x. Proof. by rewrite superopE lfunE. Qed.
Lemma opp_soE (f : superop) x : (- f) x = - f x. Proof. by rewrite superopE lfunE. Qed.
Lemma sum_soE I (r : seq I) (P : pred I) (fs : I -> superop) x :
  (\sum_(i <- r | P i) fs i) x = \sum_(i <- r | P i) fs i x.
Proof. by elim/big_rec2: _ => [|i _ f _ <-]; rewrite superopE lfunE. Qed.
Lemma scale_soE k (f : superop) x : (k *: f) x = k *: f x. Proof. by rewrite superopE lfunE. Qed.

End SuperOperator.

Notation "''SO' ( S , T )" := (@superop S T) : type_scope.
Notation "''SO' ( S )" := ('SO(S,S)) : type_scope.
Notation "''SO[' H ]_ ( S , T )" := ('SO ('H[H]_S , 'H[H]_T)) (only parsing): type_scope.
Notation "''SO[' H ]_ S" := 'SO[H]_(S, S) (only parsing) : type_scope.
Notation "''SO[' H ]_ ( S )" := 'SO[H]_S (only parsing) : type_scope.
Notation "''SO_' ( S , T )" := 'SO[_]_(S, T) : type_scope.
Notation "''SO_' S" := 'SO_(S, S) : type_scope.
Notation "''SO_' ( S )" := 'SO_S (only parsing) : type_scope.
Notation "''SO'" := (@superop _ _) (only parsing) : type_scope.
Notation SOType F := (superof_of_fun superop_key F).

Section CompSuperopDef.
Definition idso (T:chsType) : 'SO(T):= superof_of_fun superop_key \1%VF.
Definition comp_so (U V W : chsType) (A : 'SO(U,V)) (B : 'SO(W,U)) := 
    superof_of_fun superop_key ((so_val A) \o (so_val B))%VF.
Definition comp_sor (U V W : chsType) (A : 'SO(U,V)) (B : 'SO(V,W)) := 
    superof_of_fun superop_key ((so_val B) \o (so_val A))%VF.
End CompSuperopDef.
Arguments idso {T}.
Notation ":1" := (@idso _).
Notation "E ':o' F" := (comp_so E F) : lfun_scope.
Notation "E 'o:' F" := (comp_sor E F) : lfun_scope.
Lemma comp_soElr (U V W : chsType) (f : 'SO(U,V)) (g : 'SO(W,U)) : 
  (f :o g) = g o: f. 
Proof. by []. Qed.
Lemma comp_soErl (U V W : chsType) (f : 'SO(U,V)) (g : 'SO(V,W)) : 
  (f o: g) = g :o f. 
Proof. by []. Qed.

Notation "\compl_ ( i <- r | P ) F" := 
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i <- r | P%B) F%VF ) : lfun_scope.
Notation "\compl_ ( i <- r ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i <- r) F%VF) : lfun_scope.
Notation "\compl_ ( m <= i < n | P ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_( m%N <= i < n%N | P%B) F%VF)%BIG) 
    : lfun_scope.
Notation "\compl_ ( m <= i < n ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_(m%N <= i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compl_ ( i | P ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i | P%B) F%VF) : lfun_scope.
Notation "\compl_ i F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_i F%VF) : lfun_scope.
Notation "\compl_ ( i : t | P ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i : t | P%B) F%VF) (only parsing) 
    : lfun_scope.
Notation "\compl_ ( i : t ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i : t) F%VF) (only parsing) : lfun_scope.
Notation "\compl_ ( i < n | P ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_(i < n%N | P%B) F%VF)%BIG) : lfun_scope.
Notation "\compl_ ( i < n ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_(i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compl_ ( i 'in' A | P ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i in A | P%B) F%VF) : lfun_scope.
Notation "\compl_ ( i 'in' A ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i in A) F%VF) : lfun_scope.

Notation "\compr_ ( i <- r | P ) F" := 
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i <- r | P%B) F%VF ) : lfun_scope.
Notation "\compr_ ( i <- r ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i <- r) F%VF) : lfun_scope.
Notation "\compr_ ( m <= i < n | P ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_( m%N <= i < n%N | P%B) F%VF)%BIG) 
    : lfun_scope.
Notation "\compr_ ( m <= i < n ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_(m%N <= i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compr_ ( i | P ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i | P%B) F%VF) : lfun_scope.
Notation "\compr_ i F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_i F%VF) : lfun_scope.
Notation "\compr_ ( i : t | P ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i : t | P%B) F%VF) (only parsing) 
    : lfun_scope.
Notation "\compr_ ( i : t ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i : t) F%VF) (only parsing) : lfun_scope.
Notation "\compr_ ( i < n | P ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_(i < n%N | P%B) F%VF)%BIG) : lfun_scope.
Notation "\compr_ ( i < n ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_(i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compr_ ( i 'in' A | P ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i in A | P%B) F%VF) : lfun_scope.
Notation "\compr_ ( i 'in' A ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i in A) F%VF) : lfun_scope.

Section CompSuperop.
Variable (U V W T: chsType).
Implicit Types (f : 'SO(W, T)) (g : 'SO(V, W)) (h : 'SO(U, V)).

Lemma id_soE (K : chsType) (u : 'End(K)) : :1 u = u .
Proof. by rewrite superopE !lfunE. Qed.

Lemma comp_soE f g u : (f :o g) u = f (g u). Proof. by rewrite superopE !lfunE. Qed.

Lemma comp_soA f g h : (f :o (g :o h) = (f :o g) :o h).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunA. Qed.

Lemma comp_so1l f : (:1 :o f) = f.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1l. Qed.

Lemma comp_so1r f : (f :o :1) = f.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1r. Qed.

Lemma comp_so0l g : (0 :o g) = 0 :> 'SO(V, T).
Proof. by apply/val_inj; rewrite /= !soK comp_lfun0l. Qed.

Lemma comp_so0r f : (f :o 0) = 0 :> 'SO(V, T).
Proof. by apply/val_inj; rewrite /= !soK comp_lfun0r. Qed.

Lemma comp_soDl f1 f2 g : ((f1 + f2) :o g = (f1 :o g) + (f2 :o g)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunDl. Qed.

Lemma comp_soDr f g1 g2 : (f :o (g1 + g2) = (f :o g1) + (f :o g2)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunDr. Qed.

Lemma comp_soNl f g : ((- f) :o g = - (f :o g)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunNl. Qed.

Lemma comp_soNr f g : (f :o (- g) = - (f :o g)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunNr. Qed.

Lemma comp_soZl (k : C) f g : (k *: (f :o g) = (k *: f) :o g).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunZl. Qed.

Lemma comp_soZr (k : C) f g : (k *: (f :o g) = f :o (k *: g)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunZr. Qed.

Lemma comp_sorE g f u : (g o: f) u = f (g u). Proof. by rewrite superopE !lfunE. Qed.

Lemma comp_sorA h g f : (h o: (g o: f) = (h o: g) o: f).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunA. Qed.

Lemma comp_sor1l g : (:1 o: g) = g.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1r. Qed.

Lemma comp_sor1r g : (g o: :1) = g.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1l. Qed.

Lemma comp_sor0l f : (0 o: f) = 0 :> 'SO(V, T).
Proof. by apply/val_inj; rewrite /= !soK comp_lfun0r. Qed.

Lemma comp_sor0r g : (g o: 0) = 0 :> 'SO(V, T).
Proof. by apply/val_inj; rewrite /= !soK comp_lfun0l. Qed.

Lemma comp_sorDl g1 g2 f : ((g1 + g2) o: f = (g1 o: f) + (g2 o: f)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunDr. Qed.

Lemma comp_sorDr g f1 f2 : (g o: (f1 + f2) = (g o: f1) + (g o: f2)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunDl. Qed.

Lemma comp_sorNl g f : ((- g) o: f = - (g o: f)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunNr. Qed.

Lemma comp_sorNr g f : (g o: (- f) = - (g o: f)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunNl. Qed.

Lemma comp_sorZl (k : C) g f : (k *: (g o: f) = (k *: g) o: f).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunZr. Qed.

Lemma comp_sorZr (k : C) g f : (k *: (g o: f) = g o: (k *: f)).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunZl. Qed.

End CompSuperop.

Section KrausSuperop.
Variable (U V: chsType).

Definition krausso_fun (F : finType) (f : F -> 'Hom(U,V)) :
  [vectType C of 'End(U)] -> [vectType C of 'End(V)] :=
  (fun x : [vectType C of 'End(U)] => \sum_i ((f i) \o x \o (f i)^A)).
Lemma krausso_fun_is_linear F f : linear (@krausso_fun F f).
Proof. 
move=>a x y; rewrite /krausso_fun linear_sum -big_split/=.
by apply eq_bigr=>i _; rewrite linearPr linearPl.
Qed.
Canonical krausso_fun_linear F f := Linear (@krausso_fun_is_linear F f).
Definition krausso F f := Superop (linfun (@krausso_fun F f)).
(* without key, prevent rewrite of superopE *)

Lemma kraussoE F f x : (@krausso F f) x = \sum_i ((f i) \o x \o (f i)^A).
Proof. by rewrite /krausso /fun_of_superof/= lfunE. Qed.

Lemma krausso_reindex (I J : finType) (h : J -> I)
  (F : I -> 'Hom(U,V)) (G : J -> 'Hom(U,V)) :
  bijective h -> (forall j, F (h j) = G j ) ->
  krausso F = krausso G.
Proof.
move=>[g hK gK] P1. apply/superopP=>x.
rewrite !kraussoE (@reindex _ _ _ _ _ h)//=.
exists g=>s _//. by apply eq_bigr=>i _; rewrite P1.
Qed.

Definition formso f := krausso (fun _ : 'I_1 =>f).

Lemma formsoE f x : (formso f) x = f \o x \o f^A. 
Proof. by rewrite kraussoE big_ord1. Qed.

Lemma formso0 : (formso 0) = 0.
Proof. by apply/superopP=>x; rewrite formsoE abort_soE !comp_lfun0l. Qed.

End KrausSuperop.

Section IfSuperop.
Variable (U V W: chsType).

Definition ifso_fun (F : finType) (f : F -> 'Hom(U,V)) (br : forall (i : F), 'SO(V,W)):
  [vectType C of 'End(U)] -> [vectType C of 'End(W)] :=
  (fun x : [vectType C of 'End(U)] => \sum_i (br i ((f i) \o x \o (f i)^A))).
Lemma ifso_fun_is_linear F f br : linear (@ifso_fun F f br).
Proof. 
move=>a x y; rewrite /ifso_fun linear_sum -big_split/=.
by apply eq_bigr=>i _; rewrite linearPr linearPl linearP.
Qed.
Canonical ifso_fun_linear F f br := Linear (@ifso_fun_is_linear F f br).
Definition ifso F f br := Superop (linfun (@ifso_fun F f br)).

Lemma ifsoE F f br x : (@ifso F f br) x = \sum_i (br i ((f i) \o x \o (f i)^A)).
Proof. by rewrite /ifso /fun_of_superof/= lfunE. Qed.

End IfSuperop.

Section KrausSuperopExtra.

Lemma formso1 (U : chsType) : formso (\1 : 'End(U)) = :1.
Proof. by apply/superopP=>x; rewrite formsoE adjf1 id_soE comp_lfun1l comp_lfun1r. Qed.

Lemma comp_krausso (U V W : chsType) (F G : finType) (f : F -> 'Hom(U,V)) 
  (g : G -> 'Hom(W,U)) :
  krausso f :o krausso g = krausso (fun i : F * G => f i.1 \o g i.2).
Proof.
apply/superopP=>x. rewrite comp_soE !kraussoE.
under eq_bigr do rewrite linear_sumr linear_suml/=.
by rewrite pair_big/=; apply eq_bigr=>i _; rewrite adjf_comp !comp_lfunA.
Qed.

Lemma compr_krausso (U V W : chsType) (F G : finType) (f : F -> 'Hom(U,V)) 
  (g : G -> 'Hom(V, W)) :
  krausso f o: krausso g = krausso (fun i : F * G => g i.2 \o f i.1).
Proof.
apply/superopP=>x. rewrite comp_soE !kraussoE.
under eq_bigr do rewrite linear_sumr linear_suml/=.
by rewrite exchange_big pair_big/=; apply eq_bigr=>i _; rewrite adjf_comp !comp_lfunA.
Qed.

Lemma ifso_krausso (U V W : chsType) (F : finType) (f : F -> 'Hom(U,V)) 
  (G : F -> finType) (br : forall (i : F), G i -> 'Hom(V,W)) :
  ifso f (fun i=>krausso (br i)) = 
  krausso (fun i : {i : F & G i} => br (tag i) (tagged i) \o f (tag i)).
Proof.
apply/superopP=>x. rewrite ifsoE !kraussoE.
under eq_bigr do rewrite kraussoE.
by rewrite sig_big_dep/=; apply eq_bigr=>i _; rewrite adjf_comp !comp_lfunA. 
Qed.

Lemma krausso_ord (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) :
  krausso f = krausso (fun i : 'I_#|F| =>f (enum_val i)).
Proof.
apply/superopP=>x; rewrite !kraussoE; apply: reindex.
by exists enum_rank=>a _; rewrite ?enum_rankK// enum_valK.
Qed.

Lemma addso_krausso (U V : chsType) (F G : finType) (f : F -> 'Hom(U,V)) 
  (g : G -> 'Hom(U,V)) :
  krausso f + krausso g = krausso (fun i : F + G => 
  match i with inl j => f j | inr k => g k end).
Proof. by apply/superopP=>x; rewrite add_soE !kraussoE big_sumType/=. Qed.

Lemma scaleso_krausso (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) (c : C) :
  0 <= c -> c *: krausso f = krausso (fun i=>sqrtC c *: f i).
Proof.
move=>Pc. apply/superopP=>x; rewrite scale_soE !kraussoE.
under [RHS]eq_bigr do rewrite -!comp_lfunZl linearZ/= -!comp_lfunZr scalerA.
by rewrite -linear_sum/=; f_equal; rewrite -normCK ger0_norm ?sqrtC_ge0// sqrtCK.
Qed.

End KrausSuperopExtra.

Definition soE := (comp_soE, scale_soE, opp_soE, add_soE, sum_soE, abort_soE, 
  id_soE, superopE, formsoE, kraussoE).

Lemma comp_soACA (U1 U2 U3 U4 U5 : chsType) (A: 'SO(U4,U5)) (B: 'SO(U3,U4))
(C: 'SO(U2,U3)) (D: 'SO(U1,U2)) :
  A :o B :o C :o D = A :o (B :o C) :o D.
Proof. by rewrite !comp_soA. Qed.

Lemma comp_sorACA (U1 U2 U3 U4 U5 : chsType) (A: 'SO(U1,U2)) (B: 'SO(U2,U3))
(C: 'SO(U3,U4)) (D: 'SO(U4,U5)) :
  A o: B o: C o: D = A o: (B o: C) o: D.
Proof. by rewrite !comp_sorA. Qed.

Section BiLinearCompso.
Variable (U V W : chsType).

Lemma linear_comp_so f : linear (@comp_so U V W f).
Proof. by move=>a u v; rewrite comp_soDr comp_soZr. Qed. 
Canonical comp_so_linear f := Linear (@linear_comp_so f).
Definition comp_so_r f := (@comp_so U V W)^~ f.
Lemma linear_comp_so_r f : linear (@comp_so_r f).
Proof. by move=>a u v; rewrite /comp_so_r comp_soDl comp_soZl. Qed.
Canonical comp_so_r_linear f := Linear (@linear_comp_so_r f).
Canonical comp_so_rev := [revop comp_so_r of (@comp_so U V W)].
Canonical comp_so_is_bilinear := [bilinear of (@comp_so U V W)].

Lemma linear_comp_sor f : linear (@comp_sor U V W f).
Proof. by move=>a u v; rewrite comp_sorDr comp_sorZr. Qed. 
Canonical comp_sor_linear f := Linear (@linear_comp_sor f).
Definition comp_sor_r f := (@comp_sor U V W)^~ f.
Lemma linear_comp_sor_r f : linear (@comp_sor_r f).
Proof. by move=>a u v; rewrite /comp_sor_r comp_sorDl comp_sorZl. Qed.
Canonical comp_sor_r_linear f := Linear (@linear_comp_sor_r f).
Canonical comp_sor_rev := [revop comp_sor_r of (@comp_sor U V W)].
Canonical comp_sor_is_bilinear := [bilinear of (@comp_sor U V W)].

End BiLinearCompso.

Section SOVectType.
Variable (U V: chsType).

Lemma so_vect_iso : Vector.axiom (Vector.dim [vectType C of 'End(U)] *
Vector.dim [vectType C of 'End(V)]) 'SO(U,V).
Proof.
move: (lfun_vect_iso [vectType C of 'End(U)] [vectType C of 'End(V)])=>[f lf bf].
exists (f \o @so_val U V)%FUN.
by move=>a x y; rewrite /= linearP/= lf.
apply bij_comp=>//. exists (@Superop U V).
by move=>x; apply/val_inj. by move=>x.
Qed.
Definition so_vectMixin := VectMixin so_vect_iso.
Canonical so_vectType := VectType C 'SO(U,V) so_vectMixin.

End SOVectType.

Module HermitianTopology.
Import Pointed.Exports Filtered.Exports Topological.Exports Uniform.Exports PseudoMetric.Exports.
Import Complete.Exports CompletePseudoMetric.Exports CTopology.Exports.
Import FinNormedModule.Exports VNorm.Exports.

Section HermitianTopology.
Variable (V: hermitianType).

Local Canonical hermitian_pointedType := [pointedType of V for pointed_of_zmodule [zmodType of V]].
Local Canonical hermitian_filteredType := [filteredType V of V for filtered_of_normedZmod [normedZmodType C of V]].
Local Canonical hermitian_topologicalType := TopologicalType V (topologyOfEntourageMixin (uniformityOfBallMixin
                                 (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Local Canonical hermitian_uniformType := UniformType V (uniformityOfBallMixin
                            (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)).
Local Canonical hermitian_pseudoMetricType := 
  PseudoMetricType V (pseudoMetric_of_normedDomain [normedZmodType C of V]).

Lemma hermitian_norm_ball :
  @ball _ [pseudoMetricType (complex_numDomainType hermitian.R) of V] = ball_ (fun x => `| x |).
Proof. by rewrite /normr /ball_ predeq3E/= /ball/=/normr/=. Qed.

Definition hermitian_PseudoMetricNormedZmodMixin := PseudoMetricNormedZmodule.Mixin hermitian_norm_ball.
Local Canonical hermitian_pseudoMetricNormedZmodType := PseudoMetricNormedZmodType C V hermitian_PseudoMetricNormedZmodMixin.

Definition hermitian_NormedModMixin := NormedModMixin (@normrZ V).
Local Canonical hermitian_normedModType := NormedModType C V hermitian_NormedModMixin.
Local Canonical hermitian_finNormedModType := Eval hnf in (FinNormedModType C V).
Local Canonical hermitian_completeType := Eval hnf in 
  (CompleteType V (@V_complete _ [finNormedModType C of V])).
Local Canonical hermitian_CompleteNormedModule := Eval hnf in [completeNormedModType C of V].

End HermitianTopology.

Section CHSTopology.
Variable (V: chsType).

Local Canonical chs_pointedType := [pointedType of V for pointed_of_zmodule [zmodType of V]].
Local Canonical chs_filteredType := [filteredType V of V for filtered_of_normedZmod [normedZmodType C of V]].
Local Canonical chs_topologicalType := TopologicalType V (topologyOfEntourageMixin (uniformityOfBallMixin
                                 (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Local Canonical chs_uniformType := UniformType V (uniformityOfBallMixin
                            (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)).
Local Canonical chs_pseudoMetricType := 
  PseudoMetricType V (pseudoMetric_of_normedDomain [normedZmodType C of V]).
Local Canonical chs_pseudoMetricNormedZmodType := 
  Eval hnf in PseudoMetricNormedZmodType C V (hermitian_PseudoMetricNormedZmodMixin V).
Local Canonical chs_normedModType := Eval hnf in NormedModType C V (hermitian_NormedModMixin V).

Local Canonical chs_finNormedModType := Eval hnf in (FinNormedModType C V).
Local Canonical chs_completeType := Eval hnf in 
  (CompleteType V (@V_complete _ [finNormedModType C of V])).
Local Canonical chs_CompleteNormedModule := Eval hnf in [completeNormedModType C of V].

End CHSTopology.

Section LfunTopology.
Variable (U V: chsType).

Local Notation F := 'Hom(U,V).
Definition trfnorm (f: F) := \tr| f2mx f |.

Lemma trfnorm0_eq0 (f: F) : trfnorm f = 0 -> f = 0.
Proof. by rewrite /trfnorm=>/trnorm0_eq0 P1; apply/f2mx_inj; rewrite P1 linear0. Qed.

Lemma trfnorm_triangle (f g: F) : trfnorm (f + g) <= trfnorm f + trfnorm g.
Proof. rewrite /trfnorm linearD/=. exact: trnorm_triangle. Qed.

Lemma trfnormZ (a: C) (f: F) : trfnorm (a *: f) = `|a| * trfnorm f.
Proof. rewrite /trfnorm linearZ/=. exact: trnormZ. Qed.

Canonical trfnorm_vnorm := Vnorm trfnorm_triangle trfnorm0_eq0 trfnormZ.

Lemma trfnormMn (f: F) n : trfnorm (f *+ n) = trfnorm f *+ n.
Proof. exact: normvMn. Qed.

Lemma trfnormN (f: F) : trfnorm (- f) = trfnorm f.
Proof. exact: normvN. Qed.

Definition lfun_normedZmodMixin := 
    Num.NormedMixin trfnorm_triangle trfnorm0_eq0 trfnormMn trfnormN.
Local Canonical lfun_normedZmodType :=
    Eval hnf in NormedZmodType C F lfun_normedZmodMixin.

Local Canonical lfun_pointedType := [pointedType of F for pointed_of_zmodule [zmodType of F]].
Local Canonical lfun_filteredType := [filteredType F of F for filtered_of_normedZmod [normedZmodType C of F]].
Local Canonical lfun_topologicalType := (TopologicalType F (topologyOfEntourageMixin (uniformityOfBallMixin
                                 (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))).
Local Canonical lfun_uniformType := (UniformType F (uniformityOfBallMixin
                            (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Local Canonical lfun_pseudoMetricType := (PseudoMetricType F (pseudoMetric_of_normedDomain [normedZmodType C of F])).

Lemma lfun_norm_ball :
  @ball _ [pseudoMetricType (complex_numDomainType hermitian.R) of F] = ball_ (fun x => `| x |).
Proof. by rewrite /normr /ball_ predeq3E/= /ball/=/normr/=. Qed.

Definition lfun_PseudoMetricNormedZmodMixin := PseudoMetricNormedZmodule.Mixin lfun_norm_ball.
Local Canonical lfun_pseudoMetricNormedZmodType := PseudoMetricNormedZmodType C F lfun_PseudoMetricNormedZmodMixin.

Definition lfun_NormedModMixin := NormedModMixin trfnormZ.
Local Canonical lfun_normedModType := NormedModType C F lfun_NormedModMixin.

Local Canonical lfun_finNormedModType := Eval hnf in (FinNormedModType C F).
Local Canonical lfun_completeType := Eval hnf in 
  (CompleteType F (@V_complete _ [finNormedModType C of F])).
Local Canonical lfun_CompleteNormedModule := Eval hnf in [completeNormedModType C of F].

End LfunTopology.

Section SuperopTopology.
Variable (U V: chsType).

Local Notation F := 'SO(U,V).
Definition trsfnorm (f: F) := \tr| f2mx (so_val f) |.

Lemma trsfnorm0_eq0 (f: F) : trsfnorm f = 0 -> f = 0.
Proof. by move/trnorm0_eq0=>P1; apply/val_inj/f2mx_inj; rewrite P1/= !linear0. Qed.

Lemma trsfnorm_triangle (f g: F) : trsfnorm (f + g) <= trsfnorm f + trsfnorm g.
Proof. rewrite /trsfnorm !linearD/=. exact: trnorm_triangle. Qed.

Lemma trsfnormZ (a: C) (f: F) : trsfnorm (a *: f) = `|a| * trsfnorm f.
Proof. rewrite /trsfnorm !linearZ/=. exact: trnormZ. Qed.

Canonical trsfnorm_vnorm := Vnorm trsfnorm_triangle trsfnorm0_eq0 trsfnormZ.

Lemma trsfnormMn (f: F) n : trsfnorm (f *+ n) = trsfnorm f *+ n.
Proof. exact: normvMn. Qed.

Lemma trsfnormN (f: F) : trsfnorm (- f) = trsfnorm f.
Proof. exact: normvN. Qed.

Definition superop_normedZmodMixin := 
    Num.NormedMixin trsfnorm_triangle trsfnorm0_eq0 trsfnormMn trsfnormN.
Local Canonical superop_normedZmodType :=
    Eval hnf in NormedZmodType C F superop_normedZmodMixin.

Local Canonical superop_pointedType := [pointedType of F for pointed_of_zmodule [zmodType of F]].
Local Canonical superop_filteredType := [filteredType F of F for filtered_of_normedZmod [normedZmodType C of F]].
Local Canonical superop_topologicalType := (TopologicalType F (topologyOfEntourageMixin (uniformityOfBallMixin
                                 (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))).
Local Canonical superop_uniformType := (UniformType F (uniformityOfBallMixin
                            (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Local Canonical superop_pseudoMetricType := (PseudoMetricType F (pseudoMetric_of_normedDomain [normedZmodType C of F])).

Lemma superop_norm_ball :
  @ball _ [pseudoMetricType (complex_numDomainType hermitian.R) of F] = ball_ (fun x => `| x |).
Proof. by rewrite /normr /ball_ predeq3E/= /ball/=/normr/=. Qed.

Definition superop_PseudoMetricNormedZmodMixin := PseudoMetricNormedZmodule.Mixin superop_norm_ball.
Local Canonical superop_pseudoMetricNormedZmodType := PseudoMetricNormedZmodType C F superop_PseudoMetricNormedZmodMixin.

Definition superop_NormedModMixin := NormedModMixin trsfnormZ.
Local Canonical superop_normedModType := NormedModType C F superop_NormedModMixin.

Local Canonical superop_finNormedModType := Eval hnf in (FinNormedModType C F).
Local Canonical superop_completeType := Eval hnf in 
  (CompleteType F (@V_complete _ [finNormedModType C of F])).
Local Canonical superop_CompleteNormedModule := Eval hnf in [completeNormedModType C of F].

End SuperopTopology.

Module Import Exports.
Canonical hermitian_pointedType.
Canonical hermitian_filteredType.
Canonical hermitian_topologicalType.
Canonical hermitian_uniformType.
Canonical hermitian_pseudoMetricType.
Canonical hermitian_pseudoMetricNormedZmodType.
Canonical hermitian_normedModType.
Canonical hermitian_finNormedModType.
Canonical hermitian_completeType.
Canonical hermitian_CompleteNormedModule.
Canonical chs_pointedType.
Canonical chs_filteredType.
Canonical chs_topologicalType.
Canonical chs_uniformType.
Canonical chs_pseudoMetricType.
Canonical chs_pseudoMetricNormedZmodType.
Canonical chs_normedModType.
Canonical chs_finNormedModType.
Canonical chs_completeType.
Canonical chs_CompleteNormedModule.
Canonical lfun_normedZmodType.
Canonical lfun_pointedType.
Canonical lfun_filteredType.
Canonical lfun_topologicalType.
Canonical lfun_uniformType.
Canonical lfun_pseudoMetricType.
Canonical lfun_pseudoMetricNormedZmodType.
Canonical lfun_normedModType.
Canonical lfun_finNormedModType.
Canonical lfun_completeType.
Canonical lfun_CompleteNormedModule.
Canonical superop_normedZmodType.
Canonical superop_pointedType.
Canonical superop_filteredType.
Canonical superop_topologicalType.
Canonical superop_uniformType.
Canonical superop_pseudoMetricType.
Canonical superop_pseudoMetricNormedZmodType.
Canonical superop_normedModType.
Canonical superop_finNormedModType.
Canonical superop_completeType.
Canonical superop_CompleteNormedModule.
End Exports.

Module Theory.
Section Theory.
Local Open Scope classical_set_scope.
(* since trivial mx is not normedModType, we cannot use linear_continuous *)
(* linear_continuous : U -> mx   mx -> U *)

Lemma hermitian_hausdorff (U : hermitianType) : hausdorff_space [topologicalType of U].
Proof. exact: Vhausdorff. Qed.

Lemma chs_hausdorff (U : chsType) : hausdorff_space [topologicalType of U].
Proof. exact: Vhausdorff. Qed.

Lemma lfun_hausdorff (U V: chsType) : hausdorff_space [topologicalType of 'Hom(U,V)].
Proof. exact: Vhausdorff. Qed.

Lemma superop_hausdorff (U V: chsType) : hausdorff_space [topologicalType of 'SO(U,V)].
Proof. exact: Vhausdorff. Qed.

Lemma f2mx_continuous (U V: chsType) : continuous (@f2mx _ U V).
Proof. exact: linear_to_cmx_continuous. Qed.

Lemma vecthom_continuous (U V: chsType) : continuous (@Vector.Hom _ U V).
Proof. exact: linear_of_cmx_continuous. Qed.

Lemma f2mx_cvgE (U V: chsType) (f : nat -> 'Hom(U,V)) (a : 'Hom(U,V)) :
  f --> a = ((f2mx \o f)%FUN --> f2mx a).
Proof. apply: (bijective_to_cmx_cvgE _ f2mx_bij); exact: linearP. Qed.

Lemma f2mx_is_cvgE (U V: chsType) (f : nat -> 'Hom(U,V)) :
  cvg f = cvg (f2mx \o f)%FUN.
Proof. apply: (bijective_to_cmx_is_cvgE _ f2mx_bij); exact: linearP. Qed.

Lemma f2mx_limE (U V: chsType) (f : nat -> 'Hom(U,V)) :
  cvg f -> lim (f2mx \o f)%FUN = f2mx (lim f).
Proof. apply: (bijective_to_cmx_limE _ f2mx_bij); exact: linearP. Qed.

End Theory.

End Theory.

End HermitianTopology.

Section LfunVOrderFinNomredMod.
Import HermitianTopology.Exports HermitianTopology.Theory VOrderFinNormedModule.Exports.
Local Open Scope classical_set_scope.
Variable (U : chsType).

Lemma closed_gef0 : closed [set x : 'End(U) | (0 : 'End(U)) ⊑ x].
Proof.
rewrite (_ : mkset _ = f2mx @^-1` [set y | (0 : 'M__) ⊑ y]).
by apply/funext=>y/=; rewrite lef_mx linear0.
move: (@closed_gemx _ (Vector.dim U) (0 : 'M[C]__)).
apply: closed_comp=>x _; apply f2mx_continuous.
Qed.

Definition lfun_vorderFinNormedModMixin := VOrderFinNormedModMixin closed_gef0.
Canonical lfun_vorderFinNormedModType := VOrderFinNormedModType C 'End(U) lfun_vorderFinNormedModMixin.

End LfunVOrderFinNomredMod.

Section ClosedLfSet.
Import HermitianTopology.Exports HermitianTopology.Theory CTopology.Exports.
Import FinNormedModule.Exports.
Local Open Scope classical_set_scope.
Variable (U : chsType).

Lemma closed_lef (g : 'End(U)) : closed [set f : 'End(U) | f ⊑ g].
Proof. exact: closed_lev. Qed.

Lemma closed_gef (g : 'End(U)) : closed [set f : 'End(U) | g ⊑ f].
Proof. exact: closed_gev. Qed.

Lemma closed_psdlf : closed [set f : 'End(U) | f \is psdlf].
Proof.
rewrite (_ : mkset _ = [set y | (0 : 'End(U)) ⊑ y]).
by apply/funext=>y/=; rewrite psdlfE. apply closed_gev.
Qed.

Lemma trlf_continuous : continuous (@lftrace U).
Proof. exact: linear_continuous. Qed.

Lemma closed_letrlf (x : C) : closed [set f : 'End(U) | \Tr f <= x].
Proof.
rewrite (_ : mkset _ = (@lftrace U) @^-1` [set y | y <= x])%classic.
by apply/funext=>y. apply: closed_linear. apply/cclosed_le.
Qed.

Lemma closed_getrf (x : C) : closed [set f : 'End(U) | x <= \Tr f].
Proof.
rewrite (_ : mkset _ = (@lftrace U) @^-1` [set y | x <= y])%classic.
by apply/funext=>y. apply: closed_linear. apply/cclosed_ge.
Qed.

Lemma closed_denlf : closed [set f : 'End(U) | f \is denlf].
Proof.
rewrite (_ : mkset _ = [set f | f \is psdlf] `&` [set f | \Tr f <= 1]).
by apply/funext=>y/=; rewrite propeqE; split=>[/denlfP//|P]; apply/denlfP.
apply closedI. apply closed_psdlf. apply closed_letrlf.
Qed.

Lemma closed_obslf : closed [set f : 'End(U) | f \is obslf]%classic.
Proof.
rewrite (_ : mkset _ = [set f | (0:'End(U)) ⊑ f] `&` [set f | f ⊑ \1]).
by apply/funext=>y/=; rewrite lef_obs propeqE; split=>[/andP//|P]; apply/andP.
apply closedI. apply closed_gef. apply closed_lef.
Qed.
End ClosedLfSet.

Module LfunCPO.
Import HermitianTopology.Exports HermitianTopology.Theory CTopology.Exports.
Local Open Scope classical_set_scope.

(* FD and FO are CPO *)
Section LfunCPO.
Local Close Scope lfun_scope.
Variable (V: chsType).

Definition df2f (x : 'FD(V)) := x : 'End(V).
Definition of2f (x : 'FO(V)) := x : 'End(V).

Definition dflub (u : nat -> 'FD(V)) : 'FD(V) :=
  match lim (df2f \o u) \is denlf =P true with
  | ReflectT isden => DenfType isden
  | _ => [den of 0]
  end.

Definition oflub (u : nat -> 'FO(V)) : 'FO(V) :=
  match lim (of2f \o u) \is obslf =P true with
  | ReflectT isobs => ObsfType isobs
  | _ => [obs of 0]
  end.

Lemma chaindf2f (u : nat -> 'FD(V)) : chain u -> nondecreasing_seq (df2f \o u).
Proof. by move=>/chain_homo P m n Pmn; move: (P _ _ Pmn); rewrite leEsub. Qed.

Lemma chaindf_lb (u : nat -> 'FD(V)) : lbounded_by (0:'End(V))%VF (df2f \o u).
Proof. move=>i; apply: denf_ge0. Qed.

Lemma chaindf_ub (u : nat -> 'FD(V)) : ubounded_by (\1:'End(V))%VF (df2f \o u).
Proof. by move=>i; apply: denf_le1. Qed.

Lemma chainof2f (u : nat -> 'FO(V)) : chain u -> nondecreasing_seq (of2f \o u).
Proof. by move=>/chain_homo P m n Pmn; move: (P _ _ Pmn); rewrite leEsub. Qed.

Lemma chainof_lb (u : nat -> 'FO(V)) : lbounded_by (0:'End(V))%VF (of2f \o u).
Proof. by move=>i; apply: obsf_ge0. Qed.

Lemma chainof_ub (u : nat -> 'FO(V)) : ubounded_by (\1:'End(V))%VF (of2f \o u).
Proof. by move=>i; apply: obsf_le1. Qed.

Lemma lim_denlf (u : nat -> 'FD(V)) : 
  cvg (df2f \o u) -> [set x | x \is denlf] (lim (df2f \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (df2f \o u) _ _ _ _)=>//.
apply closed_denlf. by apply: nearW=>x; rewrite /=/df2f denf_den.
Qed.

Lemma lim_obslf (u : nat -> 'FO(V)) : 
  cvg (of2f \o u) -> [set x | x \is obslf] (lim (of2f \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (of2f \o u) _ _ _ _)=>//.
apply closed_obslf. by apply: nearW=>x; rewrite /=/of2f obsf_obs.
Qed.

Lemma dflub_lub : forall c : nat -> 'FD(V), chain c -> (forall i, c i ⊑ dflub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> dflub c ⊑ x).
Proof.
move=>c Pc. move: (chaindf2f Pc) (chaindf_ub c)=>P1 P2.
move: (vnondecreasing_is_cvg P1 P2)=>P3.
move: (nondecreasing_cvg_lev P1 P3)=>P4.
rewrite /dflub; case: eqP=>P5; last by exfalso; apply P5; apply lim_denlf.
split. by move=>i; rewrite leEsub/= P4.
by move=>x Px; rewrite leEsub/=; apply: lim_lev.
Qed.

Lemma dflub_ub : forall c : nat -> 'FD(V), chain c -> (forall i, c i ⊑ dflub c).
Proof. by move=>c /dflub_lub=>[[P1]]. Qed.

Lemma dflub_least : forall c : nat -> 'FD(V), 
  chain c -> forall x, (forall i, c i ⊑ x) -> dflub c ⊑ x.
Proof. by move=>c /dflub_lub=>[[_ ]]. Qed.

Lemma oflub_lub : forall c : nat -> 'FO(V), chain c -> (forall i, c i ⊑ oflub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> oflub c ⊑ x).
Proof.
move=>c Pc. move: (chainof2f Pc) (chainof_ub c)=>P1 P2.
move: (vnondecreasing_is_cvg P1 P2)=>P3.
move: (nondecreasing_cvg_lev P1 P3)=>P4.
rewrite /oflub; case: eqP=>P5; last by exfalso; apply P5; apply lim_obslf.
split. by move=>i; rewrite leEsub/= P4.
by move=>x Px; rewrite leEsub; apply: lim_lev.
Qed.

Lemma oflub_ub : forall c : nat -> 'FO(V), chain c -> (forall i, c i ⊑ oflub c).
Proof. by move=>c /oflub_lub=>[[P1]]. Qed.

Lemma oflub_least : forall c : nat -> 'FO(V), 
  chain c -> forall x, (forall i, c i ⊑ x) -> oflub c ⊑ x.
Proof. by move=>c /oflub_lub=>[[_ ]]. Qed.

Import CpoMixin.Exports.
Definition denlf_cpoMixin := CpoMixin (@denf_ges0 V) dflub_ub dflub_least.
Local Canonical denlf_cpoType := CpoType 'FD(V) denlf_cpoMixin.
Definition obslf_cpoMixin := CpoMixin (@obsf_ges0 V) oflub_ub oflub_least.
Local Canonical obslf_cpoType := CpoType 'FO(V) obslf_cpoMixin.

End LfunCPO.

Module Import Exports.
Canonical denlf_cpoType.
Canonical obslf_cpoType.
End Exports.

End LfunCPO.
Export LfunCPO.Exports.

Definition trace_nincr (U V : chsType) (F:finType) (f : F -> 'Hom(U,V)) 
  := (\sum_i ((f i)^A \o (f i)) ⊑ \1)%VF.

Definition trace_presv (U V : chsType) (F:finType) (f : F -> 'Hom(U,V)) 
  := (\sum_i ((f i)^A \o (f i)) == \1)%VF.

Lemma trace_presv_nincr (U V : chsType) (F:finType) (f : F -> 'Hom(U,V)) : 
  trace_presv f -> trace_nincr f.
Proof. by rewrite /trace_presv /trace_nincr=>/eqP->. Qed.



(* trace nonincreasing *)
Module TraceNincr.

Section ClassDef.
Variable (U V : chsType) (F : finType).

Notation axiom := trace_nincr.

Structure map (phUV : phant (F -> 'Hom(U,V))) := Pack {
  apply : F -> 'Hom(U,V); 
  _ : axiom apply; 
}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> 'Hom(U,V))) (f g : F -> 'Hom(U,V)) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Coercion apply : map >-> Funclass.
Notation TNType M := (Pack (Phant _) M).
Notation "''TN' ( F ; S , T )" := (map (Phant (F -> 'Hom(S,T)))) : type_scope.
Notation "''TN' ( F ; S )"     := ('TN (F; S, S)) : type_scope.
Notation "''TN'" := ('TN (_; _, _)) (only parsing): type_scope.
Notation "''TN[' H ]_ ( F ; S , T )" := (map (Phant (F -> 'Hom('H[H]_S, 'H[H]_T)))) 
  (only parsing): type_scope.
Notation "''TN[' H ]_ ( F ; S )" := ('TN[H]_(F;S,S)) (only parsing): type_scope.
Notation "''TN_' ( F ; S , T )" := ('TN[_]_(F;S,T)) : type_scope.
Notation "''TN_' ( F ; S )" := ('TN[_]_(F;S)) : type_scope.
Notation "[ 'TN' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'TN' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id) : form_scope.
End Exports.

End TraceNincr.
Export TraceNincr.Exports.

Module QMeasure.

Section ClassDef.
Variable (U V : chsType) (F : finType).

Notation axiom := trace_presv.

Structure map (phUV : phant (F -> 'Hom(U,V))) := Pack {
  apply : F -> 'Hom(U,V); 
  _ : axiom apply; 
}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> 'Hom(U,V))) (f g : F -> 'Hom(U,V)) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

Definition tnType := TraceNincr.Pack phUV (trace_presv_nincr class).
End ClassDef.

Module Exports.
Coercion apply : map >-> Funclass.
Canonical tnType.
Notation QMType M := (Pack (Phant _) M).
Notation TPType M := (QMType M) (only parsing).
Notation "''QM' ( F ; S , T )" := (map (Phant (F -> 'Hom(S,T)))) : type_scope.
Notation "''QM' ( F ; S )"     := ('QM (F; S, S)) : type_scope.
Notation "''QM'" := ('QM (_; _, _)) (only parsing): type_scope.
Notation "''QM[' H ]_ ( F ; S , T )" := (map (Phant (F -> 'Hom('H[H]_S, 'H[H]_T)))) 
  (only parsing): type_scope.
Notation "''QM[' H ]_ ( F ; S )" := ('QM[H]_(F;S,S)) (only parsing): type_scope.
Notation "''QM_' ( F ; S , T )" := ('QM[_]_(F;S,T)) : type_scope.
Notation "''QM_' ( F ; S )" := ('QM[_]_(F;S)) : type_scope.
Notation "[ 'QM' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'QM' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id) : form_scope.
End Exports.

End QMeasure.
Export QMeasure.Exports.

(* delete ?? *)
Section TraceComp.
Implicit Type (U V W: chsType).

Lemma tn_sig_mul U V W (F: finType) (f : F -> 'Hom(U,V)) (G : forall i, finType)
(br : forall (i : F), G i -> 'Hom(V,W)) : 
  trace_nincr f -> (forall i, trace_nincr (br i)) ->
  trace_nincr (fun i: {i : F & G i} => br (tag i) (tagged i) \o f (tag i)).
Proof.
move=>P1 P2; rewrite /trace_nincr.
under eq_bigr do rewrite adjf_comp !comp_lfunA comp_lfunACA.
have <-: \sum_i\sum_(j : G i) (((f i)^A \o ((br i j)^A \o br i j)) \o f i)
    = \sum_i (((f (tag i))^A \o ((br (tag i) (tagged i))^A \o br (tag i) (tagged i))) \o f (tag i)).
by rewrite sig_big_dep/=.
under eq_bigr do rewrite -linear_suml/= -linear_sumr/=.
move: P1. rewrite /trace_nincr.
apply le_trans. apply lev_sum=>i _.
rewrite -{2}[(f i)^A]comp_lfun1r. apply lef_form. apply (P2 i).
Qed.

Lemma tn_mul U V W (F G : finType) (f : F -> 'Hom(U,V))
  (g : G -> 'Hom(W,U)) : 
  trace_nincr f -> trace_nincr g ->
  trace_nincr (fun i: F * G => f i.1 \o g i.2).
Proof.
move=>P1 P2; rewrite /trace_nincr.
under eq_bigr do rewrite adjf_comp !comp_lfunA comp_lfunACA.
have <-: \sum_i\sum_j (((g j)^A \o ((f i)^A \o f i)) \o g j)
    = \sum_i (((g i.2)^A \o ((f i.1)^A \o f i.1)) \o g i.2).
by rewrite pair_big/=. rewrite exchange_big.
under eq_bigr do rewrite -linear_suml/= -linear_sumr/=.
move: P2. rewrite /trace_nincr/=.
apply: le_trans. apply lev_sum=>i _.
rewrite -{2}[(g i)^A]comp_lfun1r. apply lef_form. apply P1.
Qed.

End TraceComp.

(* delete ?? *)
Section TracePreservNonincr. 
Context {L : finType} (H: L -> chsType).
Implicit Type (S T W : {set L}).

Lemma tn_tenf1 S T W (F:finType) (f : F -> 'F[H]_(S,T)) : 
  [disjoint W & S :|: T] ->
  trace_nincr f -> trace_nincr (fun i:F => f i \⊗ (\1 : 'F[H]_W)).
Proof.
move=>P1 P2; rewrite /trace_nincr. 
rewrite (eq_bigr (fun i=> ((f i)^A \o (f i)) \⊗ (\1^A \o \1))).
move=>i _. rewrite tenf_adj tenf_comp// disjoint_sym.
by move: P1; rewrite disjointXU=>/andP[_].
move: P2; rewrite -tenf_suml /trace_nincr.
move =>P2. apply: (le_trans (lef_tenfl _ _ P2)).
rewrite disjoint_sym. by move: P1; rewrite disjointXU=>/andP[->].
all: rewrite adjf1 comp_lfun1r ?tenf11// lef01//.
Qed.

Lemma tp_tenf1 S T W (F:finType) (f : F -> 'F[H]_(S,T)) : 
  [disjoint W & S :|: T] ->
  trace_presv f -> trace_presv (fun i:F => f i \⊗ (\1 : 'F[H]_W)).
Proof.
move=>P1 P2; rewrite /trace_presv. 
rewrite (eq_bigr (fun i=> ((f i)^A \o (f i)) \⊗ (\1^A \o \1))).
move=>i _. rewrite tenf_adj tenf_comp// disjoint_sym.
by move: P1; rewrite disjointXU=>/andP[_].
move/eqP: P2; rewrite -tenf_suml /trace_presv =>->. 
by rewrite comp_lfun1r adjf1 tenf11.
Qed.

Lemma castlf_tn S T S' T' (eqS: (S = S') * (T = T')) (F:finType) (f : F -> 'F[H]_(S,T)) : 
  trace_nincr f = trace_nincr (fun i:F => castlf eqS (f i)).
Proof. 
case: eqS=>P1 P2; case: S' / P1; case: T' / P2. f_equal.
Qed.

Lemma castlf_tp S T S' T' (eqS: (S = S') * (T = T')) (F:finType) (f : F -> 'F[H]_(S,T)) : 
  trace_presv f = trace_presv (fun i:F => castlf eqS (f i)).
Proof. 
case: eqS=>P1 P2; case: S' / P1; case: T' / P2. f_equal.
Qed.

Lemma tn_eqcf S T S' T' (F : finType) (f : F -> 'F[H]_(S,T)) (g: F -> 'F[H]_(S',T')) :
  (forall i, f i =c g i) -> 
    trace_nincr f = trace_nincr g.
Proof.
move=>P; have: forall i, eq_conformlf (f i) (g i) by move=>i; apply/cf_eqcf. clear P.
rewrite /eq_conformlf; case: eqP=>[eqS|]. case: eqP=>[eqT|].
case: S' / eqS g. case: T' /eqT f=> f g P.
rewrite /trace_nincr.
by under [in RHS]eq_bigr do rewrite -P castlf_id.
all: by move=>_ P; rewrite /trace_nincr !big_pred0// !lef01.
Qed.

Lemma tp_eqcf S T S' T' (F : finType) (f : F -> 'F[H]_(S,T)) (g: F -> 'F[H]_(S',T')) :
  (forall i, f i =c g i) -> 
  trace_presv f = trace_presv g.
Proof.
move=>P; have: forall i, eq_conformlf (f i) (g i) by move=>i; apply/cf_eqcf. clear P.
rewrite /eq_conformlf; case: eqP=>[eqS|]. case: eqP=>[eqT|].
case: S' / eqS g. case: T' /eqT f=> f g P.
rewrite /trace_presv.
by under [in RHS]eq_bigr do rewrite -P castlf_id.
all: by move=>_ P; rewrite /trace_presv !big_pred0// ![0 == _]eq_sym; 
apply/negb_inj; rewrite !oner_neq0.
Qed.

End TracePreservNonincr.

From mathcomp.real_closed Require Import mxtens.

(* choimx for super operator 'Hom('End(U),'End(V))*)
Section SOChoiMatrix.
Variable (U V: chsType).
Implicit Type (E F : 'SO(U,V)).
Local Open Scope lfun_scope.

Lemma psdmx_sum m I r (P : pred I) (F: I -> 'M[C]_m) :
  (forall i, P i -> F i \is psdmx) -> \sum_(i <- r | P i) F i \is psdmx.
Proof. 
elim/big_ind: _=>[_|x y ++ Pi|i Pi /(_ _ Pi)//].
apply psdmx0. move=>/(_ Pi) Px /(_ Pi) Py; apply/(psdmx_add Px Py).
Qed.

Lemma linear_tensmx (R: comRingType) m n p q M : linear (@tensmx R m n p q M).
Proof.
move=>c A B/=. apply/matrixP=>i j. 
by rewrite !mxE mulrDr mulrA [_ * c]mulrC mulrA.
Qed.
Canonical tensmx_linear (R : comRingType) m n p q M := 
    Linear (@linear_tensmx R m n p q M).
Definition tensmxr (R: comRingType) m n p q M := (@tensmx R m n p q)^~ M.
Lemma linear_tensmxr (R: comRingType) m n p q M : linear (@tensmxr R m n p q M).
Proof.
move=>c A B/=. apply/matrixP=>i j. 
by rewrite !mxE mulrDl mulrA.
Qed.
Canonical tensmxr_linear (R: comRingType) m n p q M := 
    Linear (@linear_tensmxr R m n p q M).
Canonical tensmxr_rev (R: comRingType) m n p q := 
    [revop (@tensmxr R m n p q) of (@tensmx R m n p q)].
Canonical tensmx_is_bilinear (R: comRingType) m n p q := 
    [bilinear of (@tensmx R m n p q)].

Lemma adjmx_tens (R: numClosedFieldType) {m n p q} (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)) :
  (M *t N)^*t = M^*t *t N^*t.
Proof. by rewrite !adjmxE trmx_tens map_mxT. Qed.

Lemma mxtrace_tens (R: numClosedFieldType) {m n} (M :'M[R]_m) (N : 'M[R]_n) :
\tr (M *t N) = \tr M * \tr N.
Proof.
rewrite /mxtrace. symmetry.
rewrite mulr_suml. under eq_bigr do rewrite mulr_sumr.
under [RHS]eq_bigr do rewrite mxE.
rewrite pair_big; apply: reindex=>//=.
by exists (@mxtens_index _ _)=> k; rewrite (mxtens_indexK, mxtens_unindexK).
Qed.

Definition ptrace m n (A : 'M[C]_(m * n)) :=
  (\sum_i (1%:M *t delta_mx (0:'I_1) i) *m A *m (1%:M *t delta_mx i (0:'I_1))).

Lemma ptrace_is_linear m n : linear (@ptrace m n).
Proof.
move=>c A B; rewrite /ptrace scaler_sumr -big_split/=.
apply eq_bigr=>i _; rewrite mulmxDr mulmxDl. 
congr (_ + _); by rewrite scalemxAl scalemxAr.
Qed.
Canonical ptrace_linear m n := Linear (@ptrace_is_linear m n).

Lemma matrix_tenP (R: ringType) {m n p q} (A B : 'M[R]_(m * p, n * q)) :
  (forall i j k l, A (mxtens_index (i, j)) (mxtens_index (k, l)) = B (mxtens_index (i, j)) (mxtens_index (k, l))) -> A = B.
Proof. move=>P; apply/matrixP=>i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
by rewrite P. Qed.

Lemma lemx_trace m (M N : 'M[C]_m) : M ⊑ N -> \tr M <= \tr N.
Proof.
rewrite le_lownerE=>/psdmx_dot P1.
rewrite -subr_ge0 -linearB/= /mxtrace. apply sumr_ge0=>i _.
move: (P1 (delta_mx 0 i)). rewrite nnegrE /mxtrace big_ord1.
rewrite trmxC_delta mxE (bigD1 i)//= big1; last first.
rewrite mxE (bigD1 i)//= big1; last first.
by rewrite !mxE !eqxx mulr1 mul1r !addr0.
all: by move=>k /negPf Pf; rewrite !mxE Pf ?eqxx ?mul0r ?mulr0.
Qed.

Lemma lemx_psd_ub m (M : 'M[C]_m) : M \is psdmx -> M ⊑ (\tr M)%:M.
Proof.
move=>P1; rewrite le_lownerE. apply/psdmx_dot=>u.
rewrite nnegrE linearB/= mulmxBl/= linearB/= subr_ge0 mul_mx_scalar -scalemxAl linearZ/=.
rewrite -(psdmx_trnorm P1). apply: (le_trans _ (trnorm_inner _ _)).
by apply/real_ler_norm/hermmx_dot/psdmx_herm.
Qed. 

Lemma big_nat_mul_mxtens (T : zmodType) m n (f : 'I_(m*n) -> T) :
  \sum_i f i = \sum_i \sum_j f (mxtens_index (i,j)).
Proof.
rewrite pair_big; apply: reindex=> //=.
exists (@mxtens_unindex _ _)=> i; rewrite (mxtens_indexK, mxtens_unindexK)// => _.
by rewrite -surjective_pairing.
Qed.

Lemma tr_tens (R: ringType) {m n} (A : 'M[R]_(m * n, m * n)) :
  \tr A = \sum_i\sum_j A (mxtens_index (i, j)) (mxtens_index (i, j)).
Proof. by rewrite /mxtrace big_nat_mul_mxtens. Qed.

Lemma tr_ptrace m n (A: 'M[C]_(m*n)) : \tr A = \tr (ptrace A).
Proof.
rewrite !tr_tens/=. apply eq_bigr=>i _.
rewrite big_ord1 /ptrace/= summxE. apply eq_bigr=>j _.
rewrite mxE (bigD1 (mxtens_index (i, j)))//= big1; last first.
rewrite !tensmxE mxE (bigD1 (mxtens_index (i, j)))//= big1; last first.
by rewrite tensmxE !mxE !eqxx/= !addr0 ?(mul1r, mulr1).
all: move=>k; case: (mxtens_indexP k)=> i0 i1;
rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE/= negb_and=>
/orP[/negPf P|/negPf P]; rewrite tensmxE !mxE ?P/= 1 ? eq_sym ?P ?(mul0r,mulr0)//.
Qed.

Lemma psdmx_tens m n (A: 'M[C]_m) (B: 'M[C]_n) : 
  A \is psdmx -> B \is psdmx -> A *t B \is psdmx.
Proof.
move=>/psdmx_form[x ->] /psdmx_form[y ->].
by rewrite -tensmx_mul -adjmx_tens form_psd.
Qed. 

Lemma denmx_tens m n (A: 'M[C]_m) (B: 'M[C]_n) : 
  A \is denmx -> B \is denmx -> A *t B \is denmx.
Proof. 
move=>/denmxP [P1 P2] /denmxP [P3 P4]; apply/denmxP; split; last first.
by rewrite mxtrace_tens -[1]mulr1 ler_pmul// -psdmx_trnorm// trnorm_ge0.
move: P1 P3=>/psdmx_form[x ->] /psdmx_form[y ->].
by rewrite -tensmx_mul -adjmx_tens form_psd.
Qed. 

Lemma castmx_le1 m m' (eqm : m = m') (A: 'M[C]_m) :
  castmx (eqm,eqm) A ⊑ 1%:M = (A ⊑ 1%:M).
Proof. by case: m' / eqm; rewrite castmx_id. Qed.

Lemma castmx_eq1 m m' (eqm : m = m') (A: 'M[C]_m) :
  castmx (eqm,eqm) A == 1%:M = (A == 1%:M).
Proof. by case: m' / eqm; rewrite castmx_id. Qed.

Lemma tens_mx_scalal : forall (R : comRingType)
  (m n : nat) (c : R) (M : 'M[R]_(m,n)),
  c%:M *t M  = castmx (esym (mul1n _), esym (mul1n _)) (c *: M).
Proof.
move=> R0 m n c M; apply/matrixP=> i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
rewrite tensmxE [i0]ord1 [j0]ord1 !castmxE !mxE /= mulr1n.
by congr (_ * M _ _); apply: val_inj=> /=; rewrite mul0n add0n.
Qed.

Lemma tensmxE_mid (R: ringType) m n p q (A : 'M[R]_(m,p*q)) (B: 'M[R]_(p*q,n)) i j :
  (A *m B) i j = \sum_i1 \sum_i2 A i (mxtens_index (i1,i2)) * B (mxtens_index (i1,i2)) j.
Proof.
by rewrite mxE pair_big; apply/reindex; exists (@mxtens_unindex _ _)=> k; 
rewrite (mxtens_indexK, mxtens_unindexK) -?surjective_pairing.
Qed.

(* note that f2mx and lfun different by a ^*t, so here is delta_lf j i *)
(* whose matrix form is delta_mx i j *)
(* choimx_of : 'SO -> 'M; so_of_choimx : 'M -> 'SO; linear bijective *)
Definition so2choi E :=
  \sum_i\sum_j (delta_mx i j *t f2mx (E (delta_lf j i))).

Lemma choimx_1 E i j : 
(delta_mx (0:'I_1) i *t 1%:M) *m so2choi E *m (delta_mx j (0:'I_1) *t 1%:M)
= 1%:M *t f2mx (E (delta_lf j i)).
Proof.
rewrite /so2choi linear_sum linear_suml/=.
under eq_bigr do rewrite linear_sum linear_suml/=.
under eq_bigr do under eq_bigr do rewrite !tensmx_mul mulmx1 mul1mx !mul_delta_mx_cond.
rewrite (bigD1 i)//= [X in _ + X]big1=>[k /negPf nk|].
by rewrite big1// =>m _; rewrite eq_sym nk mulr0n mul0mx linear0l.
rewrite (bigD1 j)//= big1=>[k /negPf nk|].
by rewrite eqxx mulr1n mul_delta_mx_cond nk mulr0n linear0l.
rewrite eqxx mulr1n mul_delta_mx !addr0. f_equal. apply/matrixP=>a b.
by rewrite !mxE !ord1 !eqxx.
Qed.

Definition choi2so_fun (M : 'M[C]__) : [vectType C of 'End(U)] -> [vectType C of 'End(V)] :=
  (fun x => \sum_j \sum_i [< eb i; x (eb j) >] *:
  Vector.Hom ( castmx ((mul1n _), (mul1n _))
  ((delta_mx (0:'I_1) j *t 1%:M) *m M *m (delta_mx i (0:'I_1) *t 1%:M)))).
Lemma choi2so_fun_is_linear M : linear (choi2so_fun M).
Proof.
move=>a x y. do 2 (rewrite linear_sum -big_split/=; apply eq_bigr=>? _).
by rewrite lfunE/= lfunE/= linearP/= scalerDl scalerA.
Qed.
Canonical choi2so_fun_linear M := Linear (@choi2so_fun_is_linear M).
Definition choi2so_lfun M := linfun (choi2so_fun M).
Definition choi2so M := SOType (choi2so_lfun M).

Lemma tens1mx_inj (T : ringType) m n p: injective (@tensmx T m.+1 _ n p 1%:M).
Proof.
move=>a b /matrixP P. apply/matrixP=>i j.
move: (P (mxtens_index (0, i)) (mxtens_index (0, j))).
by rewrite !tensmxE mxE !eqxx !mul1r.
Qed.

Lemma so2choiK : cancel so2choi choi2so.
Proof.
move=>E; apply/superopP=>x; rewrite soE lfunE/= /choi2so_fun.
rewrite [in RHS](lfun_sum_delta x) linear_sum.
apply eq_bigr=>i _. rewrite [in RHS]linear_sum. apply eq_bigr=>j _.
rewrite linearZ/=. f_equal. apply/f2mx_inj/(@tens1mx_inj _ 0%N _ _).
by rewrite -choimx_1/= tens_mx_scalal scale1r castmx_comp castmx_id.
Qed.

Lemma so2choi_inj : injective so2choi.
Proof. exact: (can_inj so2choiK). Qed.

Lemma choi2so_inj : injective choi2so.
Proof.
move=>E F eqEF; apply/matrix_tenP=>a c b d.
move: eqEF=>/superopP/(_ (delta_lf b a)).
rewrite !soE !lfunE/= /choi2so_fun (bigD1 a)//= (bigD1 b)//= 2 ?big1; 
  last rewrite (bigD1 a)//= (bigD1 b)//= 2 ?big1.
1,3: by move=>i /negPf ni; rewrite delta_lf_eb linearZ/= cbase ni mulr0 scale0r.
1,2: by move=>i /negPf ni; rewrite big1// =>j _; rewrite delta_lf_eb ni scale0r linear0 scale0r.
rewrite !delta_lf_eb eqxx scale1r cbase eqxx !scale1r !addr0=>P.
inversion P as [R]; move: R=>/castmx_inj R.
suff Q (M : 'M[C]__): M (mxtens_index (a, c)) (mxtens_index (b, d)) = 
  \tr (delta_mx (0:'I_1) a *t delta_mx (0:'I_1) c *m M *m (delta_mx b (0:'I_1) *t delta_mx d (0:'I_1))).
rewrite !Q -[delta_mx 0 a]mul1mx -[delta_mx d 0]mul1mx -[delta_mx 0 c]mulmx1 -[delta_mx b 0]mulmx1.
by rewrite -!tensmx_mul -!mulmxA ![in X in _ *m X]mulmxA R !mulmxA.
rewrite /mxtrace big_ord1.
have Q: (0 : 'I_1) = mxtens_index (0 : 'I_1, 0 : 'I_1) by rewrite ord1.
rewrite {5 6}Q tensmxE_mid (bigD1 b)//= (bigD1 d)// !big1/=; 
  last rewrite tensmxE tensmxE_mid (bigD1 a)//= (bigD1 c)// !big1/=.
1,3: by move=>i /negPf ni; rewrite tensmxE !mxE ni ?andbF/= !mulr0// mul0r.
1,2: by move=>i /negPf ni; rewrite big1//= =>j _; rewrite tensmxE !mxE ni ?andbF/= !mul0r// !mulr0.
by rewrite tensmxE !mxE !eqxx !addr0 !mul1r !mulr1.
Qed.

Lemma choi2soK : cancel choi2so so2choi.
Proof. move=>E. apply/choi2so_inj. apply so2choiK. Qed.

Lemma so2choi_is_linear : linear so2choi.
Proof.
move=>a x y. rewrite /so2choi. do 2 (rewrite linear_sum -big_split; apply eq_bigr=>? _).
by rewrite !soE/= linearP linearPr.
Qed.
Canonical so2choi_linear := Linear so2choi_is_linear.

Lemma choi2so_is_linear : linear choi2so.
Proof. apply: (can2_linear so2choiK choi2soK). Qed.
Canonical choi2so_linear := Linear choi2so_is_linear.

Lemma so2choi_bij : bijective so2choi.
Proof. exists choi2so. exact: so2choiK. exact: choi2soK. Qed.

Lemma choi2so_bij : bijective choi2so.
Proof. exists so2choi. exact: choi2soK. exact: so2choiK. Qed.

Definition iscp :=
  [qualify A : 'SO(_, _) | (so2choi A \is psdmx)].
Fact iscp_key : pred_key iscp. Proof. by []. Qed.
Canonical iscp_keyed := KeyedQualifier iscp_key.

Definition isqo :=
  [qualify A : 'SO(_, _) | (so2choi A \is psdmx) && (ptrace (so2choi A) ⊑ 1%:M)].
Fact isqo_key : pred_key isqo. Proof. by []. Qed.
Canonical isqo_keyed := KeyedQualifier isqo_key.

Definition isqc :=
  [qualify A : 'SO(_, _) | (so2choi A \is psdmx) && (ptrace (so2choi A) == 1%:M)].
Fact isqc_key : pred_key isqc. Proof. by []. Qed.
Canonical isqc_keyed := KeyedQualifier isqc_key.

Lemma iscpP A : reflect ((so2choi A \is psdmx)) (A \is iscp).
Proof. by rewrite [_ \is iscp]qualifE; apply/(iffP idP). Qed.

Lemma isqoP A : reflect ((so2choi A \is psdmx) /\ (ptrace (so2choi A) ⊑ 1%:M)) (A \is isqo).
Proof. by rewrite [_ \is isqo]qualifE; apply/(iffP andP). Qed.

Lemma isqcP A : reflect ((so2choi A \is psdmx) /\ (ptrace (so2choi A) == 1%:M)) (A \is isqc).
Proof. by rewrite [_ \is isqc]qualifE; apply/(iffP andP). Qed.

Lemma isqo_cp A : A \is isqo -> A \is iscp.
Proof. by move/isqoP=>[Pp _]; apply/iscpP. Qed.

Lemma isqc_qo A : A \is isqc -> A \is isqo.
Proof. by move/isqcP=>[Pp /eqP P1]; apply/isqoP; rewrite Pp P1. Qed.

Lemma isqc_cp A : A \is isqc -> A \is iscp.
Proof. by move/isqc_qo/isqo_cp. Qed.

(* next give the construct that if isqo, then give qo *)
Definition choi2kraus (A : 'M[C]_((Vector.dim U * Vector.dim V), (Vector.dim U * Vector.dim V))) k
 := Vector.Hom (castmx (erefl _, mul1n _) 
  (\sum_i delta_mx i 0 *m (sqrtC (spectral_diag A 0 k) *: (row k (spectralmx A))) 
    *m (delta_mx i (0 : 'I_1) *t 1%:M))).

Lemma ptracefunE A : A \is psdmx ->
  ptrace A = (\sum_k f2mx ((choi2kraus A k)^A \o (choi2kraus A k)))^T *t 1%:M.
Proof.
move/diag_decomp_absorb=> P1.
rewrite {1}P1 !linear_sum linear_suml/=; apply eq_bigr=>k _. 
rewrite /ptrace f2mx_comp/= adjmx_cast/= mcextra.castmx_mul castmx_id.
set v := (sqrtC (spectral_diag A 0 k) *: row k (spectralmx A)).
apply/matrix_tenP=>a c b d; rewrite tensmxE !summxE !ord1 mxE !linear_sum/= 
  summxE [in RHS](bigD1 a)//= [in X in _ + X]big1.
move=>i /negPf ni. rewrite linear_suml summxE big1 ?mul0mx ?mxE// =>j _.
by rewrite /= !adjmxM !mulmxA trmxC_delta delta_mx_mulEl ni mul0r.
rewrite linear_suml summxE (bigD1 b)//= [in RHS]big1=>[i /negPf ni|].
by rewrite -!mulmxA delta_mx_mulEr ni mul0r.
rewrite !adjmxM -!mulmxA delta_mx_mulEr !mulmxA trmxC_delta delta_mx_mulEl.
rewrite !eqxx !mul1r !addr0 -mulmxA tensmxE_mid big_ord1 !mxE eqxx mulr1.
apply eq_bigr=>i _. rewrite mulmxA -mulmxA mxE big_ord1 mulrC. congr (_ * _).
1,2: rewrite !tensmxE_mid; do 2 (apply eq_bigr=> ? _).
by rewrite adjmx_tens trmxC_delta adjmx1 !tensmxE !mxE !eqxx/= [a == _]eq_sym [_ == i]eq_sym.
by rewrite !tensmxE !mxE !eqxx !andbT.
Qed.

Lemma choi2kraus_trace_nincr A : A \is psdmx -> 
  ptrace A ⊑ 1%:M = trace_nincr (choi2kraus A).
Proof.
move=>/ptracefunE ->.
rewrite tens_mx_scalar castmx_le1 scale1r -linear_sum/=.
by rewrite /trace_nincr -lef_tr trf1 lef_mx f2mx1.
Qed.

Lemma choi2kraus_trace_presv A : A \is psdmx -> 
  ptrace A == 1%:M = trace_presv (choi2kraus A).
Proof.
move=>/ptracefunE ->.
rewrite tens_mx_scalar castmx_eq1 scale1r -linear_sum/=.
by rewrite /trace_presv -(can_eq (@trfK _ _)) trf1 -(can_eq (@f2mxK _ _ _)) f2mx1.
Qed.

Lemma krausso2choiE (F: finType) (f : F -> 'Hom(U,V)) :
let A k := \sum_i (delta_mx (0:'I_1) i *t ((delta_mx (0:'I_1)) i *m (f2mx (f k)))) 
  in \sum_k ((A k)^*t *m (A k)) = so2choi (krausso f).
Proof.
rewrite /so2choi; under [RHS]eq_bigr do (under eq_bigr do rewrite soE 
  linear_sum linear_sumr; rewrite exchange_big).
rewrite exchange_big. apply eq_bigr=>k _.
rewrite exchange_big linear_sumr/=. apply eq_bigr=>i _.
rewrite linear_sum/= linear_suml/=. apply eq_bigr=>j _.
rewrite adjmx_tens tensmx_mul adjmxM !trmxC_delta mulmxA mulmxACA !mul_delta_mx.
by f_equal; rewrite !f2mx_comp/= mulmxA /eb/= !r2vK trmxC_delta mul_delta_mx.
Qed.

Lemma krausso2choi_psd (F: finType) (f : F -> 'Hom(U,V)) : 
  so2choi (krausso f) \is psdmx.
Proof. by rewrite -krausso2choiE; apply psdmx_sum=>k _; apply formV_psd. Qed.

Lemma ptrace_krausso2choiE (F: finType) (f : F -> 'Hom(U,V)) : 
  ptrace (so2choi (krausso f)) = (\sum_k f2mx ((f k)^A \o (f k)))^T *t 1%:M.
Proof.
rewrite -krausso2choiE linear_sum [in RHS]linear_sum [in RHS]linear_suml.
apply eq_bigr=>k _/=; apply/matrix_tenP=>a b c d.
rewrite /=/ptrace tensmxE summxE f2mx_comp !mxE [RHS]mulr_suml; apply eq_bigr=>i _/=.
rewrite !linear_sum/= linear_suml summxE/=.
under eq_bigr do rewrite linear_suml linear_sum/= linear_suml summxE/=.
under eq_bigr do under eq_bigr do rewrite adjmx_tens adjmxM !tensmx_mul !trmxC_delta
  mulmx1 mul1mx mul_delta_mx tensmxE mxE.
rewrite (bigD1 c)//= [X in _ + X]big1=>[m /negPf nm|].
by rewrite big1// =>n _; rewrite [c == m]eq_sym nm andbF mul0r.
rewrite (bigD1 a)//= big1=>[m /negPf nm|]; first by rewrite eq_sym nm mul0r.
rewrite !ord1 !eqxx mul1r mulr1 !addr0 !mulmxA delta_mx_mulEl -!mulmxA delta_mx_mulEr.
by rewrite mulmxA mxE big_ord1 delta_mx_mulEl delta_mx_mulEr !eqxx !mul1r adjmxEr mulrC.
Qed.

Lemma krausso2choi_trace_nincr (F: finType) (f : F -> 'Hom(U,V)) :
  trace_nincr f = (ptrace (so2choi (krausso f)) ⊑ 1%:M).
Proof.
rewrite ptrace_krausso2choiE tens_mx_scalar castmx_le1 scale1r -linear_sum/=.
by rewrite /trace_nincr -lef_tr trf1 lef_mx f2mx1.
Qed.

Lemma krausso2choi_trace_presv (F: finType) (f : F -> 'Hom(U,V)) :
  trace_presv f = (ptrace (so2choi (krausso f)) == 1%:M).
Proof.
rewrite ptrace_krausso2choiE tens_mx_scalar castmx_eq1 scale1r -linear_sum/=.
by rewrite /trace_presv -(can_eq (@trfK _ _)) trf1 -(can_eq (@f2mxK _ _ _)) f2mx1.
Qed.

Lemma krausso2choiK E : so2choi E \is psdmx ->
  krausso (choi2kraus (so2choi E)) = E.
Proof.
move=>P1. apply/so2choi_inj. move: P1. set M := (so2choi E).
move=>/diag_decomp_absorb P1. rewrite -krausso2choiE [RHS]P1.
apply eq_bigr=>k _. have P0: (1 = 1 * 1)%N by [].
rewrite -[RHS](@castmx_id _ _ _ (erefl _, erefl _)) -(mcextra.castmx_mul P0)/= adjmx_castV/=.
congr (_ *m _); [do 2 f_equal|]; apply/matrix_tenP=>a b c d;
rewrite castmxE !cast_ord_id  summxE /choi2kraus;
set v := (sqrtC (spectral_diag (so2choi E) 0 k) *: row k (spectralmx (so2choi E))).
all: under eq_bigr do rewrite tensmxE delta_mx_mulEr/=;
rewrite (bigD1 c)//= [X in _ + X]big1=>[i /negPf ni|].
1,3: by rewrite mxE [c == i]eq_sym ni andbF mul0r.
all: rewrite !castmxE/= !cast_ord_id summxE (bigD1 c)// big1/==>[i /negPf ni|];
  first by rewrite -mulmxA delta_mx_mulEr ni mul0r.
all: have <-: mxtens_index (0,d) = (cast_ord (esym (mul1n (Vector.dim V))) d)
  by apply/ord_inj; rewrite /= mul0n add0n.
all: rewrite -mulmxA delta_mx_mulEr !ord1 [in LHS]mxE !eqxx !mul1r !addr0 [LHS]mxE
 (bigD1 (mxtens_index (c,d)))//= big1; first by move=>i; 
  rewrite -(mxtens_unindexK i) tensmxE (inj_eq (can_inj (@mxtens_indexK _ _)))=>
  /pair_neq/=[P|P]; rewrite !mxE P/= ?mul0r ?mulr0.
all: by rewrite tensmxE !mxE !eqxx !mulr1 addr0.
Qed.

Lemma tr_choi_sep E (x: 'End(U)) (y: 'End(V)) : 
\tr (so2choi E *m (f2mx (x^T) *t (f2mx y))) = \Tr (E x \o y).
Proof.
rewrite /so2choi linear_suml/= linear_sum/=.
under eq_bigr do rewrite linear_suml/= linear_sum/=.
under eq_bigr do under eq_bigr do rewrite /= tensmx_mul mxtrace_tens -f2mx_comp.
rewrite [in RHS](lfun_sum_delta x) linear_sum linear_suml linear_sum.
apply eq_bigr=>i _. rewrite /= linear_sum linear_suml linear_sum/=.
apply eq_bigr=>j _. rewrite linearZ/= linearZl/= linearZ/=.
congr (_ * _); last by rewrite lftraceC.
rewrite /mxtrace (bigD1 i)// big1/= =>[k /negPf nk|].
by rewrite delta_mx_mulEr eq_sym nk mul0r.
rewrite delta_mx_mulEr eqxx mul1r mxE addr0 dotp_mulmx /eb unlock/= !r2vK 
  trmx_mul trmx_delta mulmxA delta_mx_mulEl mxE (bigD1 j)// big1/= =>[k /negPf nk|].
by rewrite !mxE nk andbF conjC0 mul0r.
by rewrite !mxE !eqxx conjC1 !mul1r addr0.
Qed.

Lemma choimx_preserve_order E F : 
  (so2choi E ⊑ so2choi F) -> (forall x, x \is psdlf -> E x ⊑ F x).
Proof.
rewrite le_lownerE -linearB/= =>/psdmx_form [B PB].
move=>x Px. apply/lef_psdtr=>y Py.
rewrite -subr_ge0 -linearB/= -linearBl/= -opp_soE -add_soE -tr_choi_sep.
have: (f2mx x^T *t f2mx y) \is psdmx.
apply psdmx_tens. rewrite psdmx_tr.
move: Px. 2: move: Py. 1,2: by rewrite qualifE.
move=>/psdmx_form [A ->].
by rewrite PB mulmxA mxtrace_mulC !mulmxA -mulmxA -{2}(adjmxK A) -adjmxM form_tr_ge0.
Qed.

Lemma ptrace_psd m n (A : 'M[C]_(m * n)) :
  A \is psdmx -> ptrace A \is psdmx.
Proof.
move=>/psdmx_dot P1; apply/psdmx_dot=>u.
rewrite /ptrace mulmx_sumr mulmx_suml linear_sum nnegrE sumr_ge0// => i _.
move: (P1 (u *m (1%:M *t delta_mx 0 i))).
by rewrite adjmxM adjmx_tens adjmx1 trmxC_delta nnegrE !mulmxA.
Qed.

Lemma ptrace_perserves_order m n (A B : 'M[C]_(m * n)):
  A ⊑ B -> (ptrace A ⊑ ptrace B).
Proof. rewrite !le_lownerE -linearB/=. exact: ptrace_psd. Qed.

Definition leso_def E F := (so2choi E ⊑ so2choi F).
Definition ltso_def E F := (F != E) && (leso_def E F).

Lemma leso_def_choimx E F : leso_def E F = (so2choi E ⊑ so2choi F).
Proof. by []. Qed.

Lemma ltso_def_choimx E F : ltso_def E F = (so2choi E ⊏ so2choi F).
Proof. by rewrite /ltso_def lt_def (can_eq so2choiK) leso_def_choimx. Qed.

Lemma ltso_def_def : forall E F, ltso_def E F = (F != E) && (leso_def E F).
Proof. by rewrite /ltso_def. Qed.

Lemma ltso_def_anti : antisymmetric leso_def.
Proof. by move=>x y; rewrite !leso_def_choimx -eq_le=>/eqP/so2choi_inj. Qed.

Lemma leso_def_refl : reflexive leso_def.
Proof. by move=>x; rewrite leso_def_choimx. Qed.

Lemma leso_def_trans : transitive leso_def.
Proof. by move=>x y z; rewrite !leso_def_choimx; apply le_trans. Qed.

Definition lownerso_porderMixin := LePOrderMixin 
ltso_def_def leso_def_refl ltso_def_anti leso_def_trans.

Canonical lownerso_porderType := POrderType vorder_display 'SO(U,V) lownerso_porderMixin.

Lemma leso_mx E F : E ⊑ F = (so2choi E ⊑ so2choi F).
Proof. by rewrite {1}/Order.le/= leso_def_choimx. Qed.

Lemma ltso_mx E F : E ⊏ F = (so2choi E ⊏ so2choi F).
Proof. by rewrite {1}/Order.lt/= ltso_def_choimx. Qed.

Lemma leso_add2rP (G E F : 'SO(U,V)) : E ⊑ F -> (E + G) ⊑ (F + G).
Proof. 
rewrite addrC !leso_mx -subv_ge0 -[in X in _ -> X]subv_ge0.
by rewrite !linearD/= addrA addrK.
Qed.

Lemma leso_pscale2lP (e : C) E F : 0 < e -> E ⊑ F -> (e *: E) ⊑ (e *: F).
Proof. rewrite !leso_mx !linearZ/=; exact: lev_pscale2lP. Qed.

Lemma pscaleso_lge0 E (a : C) : 
  (0 : 'SO(U,V)) ⊏ E -> (0 : 'SO(U,V)) ⊑ a *: E = (0 <= a).
Proof. rewrite leso_mx ltso_mx linear0 linearZ/=; exact: pscalev_lge0. Qed.

Import VOrder.Exports.
Definition lownerso_vorderMixin := VOrderMixin leso_add2rP leso_pscale2lP.
Canonical lownerso_vorderType := VOrderType C 'SO(U,V) lownerso_vorderMixin.

Import CanVOrder.Exports.
Definition lownerso_canVOrderMixin := CanVOrderMixin pscaleso_lge0.
Canonical lownerso_canVOrderType := CanVOrderType C 'SO(U,V) lownerso_canVOrderMixin.

End SOChoiMatrix.

Arguments so2choi {U V}.
Arguments choi2so {U V}.
Arguments iscp {U V}.
Arguments isqo {U V}.
Arguments isqc {U V}.
Arguments so2choi_bij {U V}.
Arguments choi2so_bij {U V}. 

Section ClosedSOSet.
Import HermitianTopology.Exports HermitianTopology.Theory CTopology.Exports HermitianTopology VOrderFinNormedModule.Exports.
Local Open Scope classical_set_scope.
Variable (U V : chsType).
Implicit Type (f g : 'SO(U,V)).

Lemma so2choi_continuous : continuous (@so2choi U V).
Proof. apply: (bijective_to_cmx_continuous _ so2choi_bij); exact: linearP. Qed.

Lemma choi2so_continuous : continuous (@choi2so U V).
Proof. apply: (bijective_of_cmx_continuous _ choi2so_bij); exact: linearP. Qed.

Lemma so2choi_cvgE (f : nat -> 'SO(U,V)) (a : 'SO(U,V)) :
  f --> a = ((so2choi \o f)%FUN --> so2choi a).
Proof. apply: (bijective_to_cmx_cvgE _ so2choi_bij); exact: linearP. Qed.

Lemma so2choi_is_cvgE (f : nat -> 'SO(U,V)) :
  cvg f = cvg (so2choi \o f)%FUN.
Proof. apply: (bijective_to_cmx_is_cvgE _ so2choi_bij); exact: linearP. Qed.

Lemma so2choi_limE (f : nat -> 'SO(U,V)) :
  cvg f -> lim (so2choi \o f)%FUN = so2choi (lim f).
Proof. apply: (bijective_to_cmx_limE _ so2choi_bij); exact: linearP. Qed.

Lemma closed_geso0 : closed [set E | (0 : 'SO(U,V)) ⊑ E].
Proof.
rewrite (_ : mkset _ = so2choi @^-1` [set y | (0 : 'M__) ⊑ y]).
by apply/funext=>y/=; rewrite leso_mx linear0.
apply: closed_to_cmx_linear. apply: closed_gemx.
Qed.

Definition superso_vorderFinNormedModMixin := VOrderFinNormedModMixin closed_geso0.
Canonical superso_vorderFinNormedModType := VOrderFinNormedModType C 'SO(U,V) superso_vorderFinNormedModMixin.

(* qo is a closed set among all super operators *)
Lemma closed_isqo : closed [set f : 'SO(U,V) | f \is isqo].
Proof.
rewrite (_ : mkset _ = (so2choi @^-1` [set y | (0 : 'M__) ⊑ y]) `&` 
  (so2choi @^-1` [set y | ptrace y ⊑ 1%:M])).
apply/funext=>y/=; rewrite qualifE [in RHS]le_lownerE subr0 propeqE; split=>[/andP//|[->->//]].
apply closedI; apply: closed_to_cmx_linear. apply: closed_gemx.
move: (@closed_lemx _ _ (1%:M : 'M[C]_(Vector.dim U * 1))).
apply: cmxclosed_comp. exact: linearP.
Qed.

End ClosedSOSet.

Section MxtensSwap.
Implicit Type (m n p q : nat).

Definition mxswap (R: ringType) m n p q (A : 'M[R]_(m * p, n * q)) : 'M[R]_(p * m, q * n) :=
  \matrix_(i,j) A (mxtens_index ((mxtens_unindex i).2,(mxtens_unindex i).1))
  (mxtens_index ((mxtens_unindex j).2,(mxtens_unindex j).1)).

Lemma mxswapK (R: ringType) m n p q : cancel (@mxswap R m n p q) (@mxswap R p q m n).
Proof. 
by move=>x; apply/matrixP=>i j; rewrite !mxE !mxtens_indexK/= !mxtens_unindexK.
Qed.

Lemma mxswap_is_linear (R: ringType) m n p q : linear (@mxswap R m n p q).
Proof. by move=>a x y; apply/matrixP=>i j; rewrite !mxE. Qed.
Canonical mxswap_additive (R: ringType) m n p q := Additive (@mxswap_is_linear R m n p q).
Canonical mxswap_linear (R: ringType) m n p q := Linear (@mxswap_is_linear R m n p q).

Lemma mxswap_inj (R: ringType) m n p q : injective (@mxswap R m n p q).
Proof. exact: (can_inj (@mxswapK _ _ _ _ _)). Qed.

Lemma mxswap_tens (R: comRingType) m n p q (A : 'M[R]_(m,n)) (B : 'M[R]_(p,q)) :
  mxswap (A *t B) = B *t A.
Proof.
by apply/matrix_tenP=>i j s t; rewrite mxE !tensmxE !mxtens_indexK/= mulrC.
Qed.

Lemma mxswap_trace (R: ringType) m p (A : 'M[R]_(m * p)) :
  \tr (mxswap A) = \tr A.
Proof.
rewrite !tr_tens exchange_big; apply eq_bigr=>i _; apply eq_bigr=>j _.
by rewrite mxE !mxtens_indexK/=.
Qed.

Lemma mxswap_mul (R: ringType) m n p q r s (A : 'M[R]_(m * p, n * q))
  (B : 'M[R]_(n * q, r * s)) :
  mxswap A *m mxswap B = mxswap (A *m B).
Proof.
apply/matrix_tenP=>i j k l.
rewrite !mxE big_nat_mul_mxtens exchange_big [RHS]big_nat_mul_mxtens.
apply eq_bigr=>a _; apply eq_bigr=>b _.
by rewrite !mxE !mxtens_indexK/=.
Qed.

Lemma mxswap_trmx (R: ringType) m n p q (A : 'M[R]_(m * p, n * q)) :
  ((mxswap A)^T = mxswap (A ^T))%R.
Proof. by apply/matrix_tenP=>i j k l; rewrite !mxE. Qed.

Lemma mxswap_map_mx (R: ringType) (f : {rmorphism R -> R}) m n p q (A : 'M[R]_(m * p, n * q)) :
  map_mx f (mxswap A) = mxswap (map_mx f A).
Proof. by apply/matrix_tenP=>i j k l; rewrite !mxE. Qed.

Lemma mxswap_trmxC (R: numClosedFieldType) m n p q (A : 'M[R]_(m * p, n * q)) :
  ((mxswap A)^*t = mxswap (A ^*t))%R.
Proof. by apply/matrix_tenP=>i j k l; rewrite !mxE. Qed.
End MxtensSwap.

Reserved Notation "E '^*o' " (at level 8).

(* adjoint of super operator *)
Section DualSO.
Variable (U V : chsType).

Definition dualso (E : 'SO(U,V)) := choi2so (mxswap (so2choi E)^T).
Notation "E '^*o' " := (dualso E) : lfun_scope.

Lemma dualso_trlfE (E : 'SO(U,V)) (x : 'End(U)) A :
  \Tr (E x \o A) = \Tr (x \o (E^*o A)).
Proof.
rewrite -tr_choi_sep [in RHS]lftraceC -tr_choi_sep /dualso.
rewrite -mxtrace_tr trmx_mul mxtrace_mulC choi2soK trmx_tens trmxK.
by rewrite -mxswap_trace -mxswap_mul mxswap_tens /tr_lfun/=.
Qed.

Lemma dualso_trlfEV (E : 'SO(U,V)) (x : 'End(U)) A :
  \Tr (A \o E x) = \Tr ((E^*o A) \o x).
Proof. by rewrite lftraceC dualso_trlfE lftraceC. Qed.

Lemma dualso_krausE (F: finType) (f : F -> 'Hom(U,V)) (A : 'End(V)) :
  dualso (krausso f) A = \sum_i ((f i)^A \o A \o (f i)).
Proof.
apply/eqP/trlf_introl=>x.
rewrite -dualso_trlfE soE linear_sumr linear_suml !linear_sum.
apply eq_bigr =>/= i _.
by rewrite -!comp_lfunA lftraceC !comp_lfunA.
Qed.

Lemma dualso_formE (f : 'Hom(U,V)) (A : 'End(V)) :
  dualso (formso f) A = (f^A \o A \o f).
Proof. by rewrite dualso_krausE big_ord1. Qed.
Definition dualsoE := (dualso_formE, dualso_krausE).

Lemma dualso_krausso (F: finType) (f : F -> 'Hom(U,V)) :
  dualso (krausso f) = krausso (fun i=> (f i)^A).
Proof.
by apply/superopP=>A; rewrite dualsoE soE; under [RHS]eq_bigr do rewrite adjfK.
Qed.
Lemma dualso_formso (f : 'Hom(U,V)) :
  dualso (formso f) = formso (f^A).
Proof. exact: dualso_krausso. Qed.

Lemma dualso_is_linear : linear dualso.
Proof. by move=>a x y; rewrite /dualso !linearP/=. Qed.
Canonical dualso_additive := Additive dualso_is_linear.
Canonical dualso_linear := Linear dualso_is_linear.

End DualSO.

Notation "E '^*o' " := (dualso E) : lfun_scope.

(* complete positive maps*)
Module CPMap.

Section ClassDef.
Variable (U V : chsType).
Notation axiom f := (f \is iscp).
Structure type := Pack { sort: 'SO(U,V); _ : axiom sort; }.
Local Coercion sort : type >-> superop.

Variables (T : 'SO(U,V)) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom (cT' : 'SO)) in c.
Definition clone c of phant_id class c := @Pack T c.

Local Canonical subType := Eval hnf in [subType for sort].
Definition eqMixin := Eval hnf in [eqMixin of type by <:].
Local Canonical  eqType  := Eval hnf in EqType type eqMixin.
Definition choiceMixin := [choiceMixin of type by <:].
Local Canonical  choiceType  := Eval hnf in ChoiceType type choiceMixin.
Definition porderMixin := [porderMixin of type by <:].
Local Canonical porderType :=
  Eval hnf in POrderType vorder_display type porderMixin.
End ClassDef.

Module Import Exports.
Coercion sort : type >-> superop.
Canonical subType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation CPType M := (@Pack _ _ _ M).
Notation "''CP' ( S , T )" := (@type S T) : type_scope.
Notation "''CP' ( S )" := ('CP(S,S)) : type_scope.
Notation "''CP'" := ('CP(_,_)) (only parsing) : type_scope.
Notation "''CP[' H ]_ ( S , T )" := ('CP('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''CP[' H ]_ S" := ('CP[H]_(S,S))   (only parsing) : type_scope.
Notation "''CP[' H ]_ ( S )" := ('CP[H]_S)    (only parsing) : type_scope.
Notation "''CP_' ( S , T )"  := ('CP[_]_(S,T)) : type_scope.
Notation "''CP_' S"  := ('CP[_]_S) : type_scope.
Notation "''CP_' ( S )" := ('CP_S) (only parsing) : type_scope.
Notation "[ 'CP' 'of' f 'as' g ]" := (@clone _ _ f g _ idfun) : form_scope.
Notation "[ 'CP' 'of' f ]" := (@clone _ _ f _ _ id) : form_scope.
End Exports.

End CPMap.
Export CPMap.Exports.

(* quantum operation - complete positive trace nonincreasing *)
Module QOperation.

Section ClassDef.
Variable (U V : chsType).
Notation axiom f := (f \is isqo).
Structure type := Pack { sort: 'SO(U,V); _ : axiom sort; }.
Local Coercion sort : type >-> superop.

Variables (T : 'SO(U,V)) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom (cT' : 'SO)) in c.
Definition clone c of phant_id class c := @Pack T c.

Local Canonical subType := Eval hnf in [subType for sort].
Definition eqMixin := Eval hnf in [eqMixin of type by <:].
Local Canonical  eqType  := Eval hnf in EqType type eqMixin.
Definition choiceMixin := [choiceMixin of type by <:].
Local Canonical  choiceType  := Eval hnf in ChoiceType type choiceMixin.
Definition porderMixin := [porderMixin of type by <:].
Local Canonical porderType :=
  Eval hnf in POrderType vorder_display type porderMixin.
Definition cpType := CPMap.Pack (isqo_cp class).

End ClassDef.

Module Import Exports.
Coercion sort : type >-> superop.
Canonical subType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical cpType.
Notation QOType M := (@Pack _ _ _ M).
Notation "''QO' ( S , T )" := (@type S T) : type_scope.
Notation "''QO' ( S )" := ('QO(S,S)) : type_scope.
Notation "''QO'" := ('QO(_,_)) (only parsing) : type_scope.
Notation "''QO[' H ]_ ( S , T )" := ('QO('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''QO[' H ]_ S" := ('QO[H]_(S,S))   (only parsing) : type_scope.
Notation "''QO[' H ]_ ( S )" := ('QO[H]_S)    (only parsing) : type_scope.
Notation "''QO_' ( S , T )"  := ('QO[_]_(S,T)) : type_scope.
Notation "''QO_' S"  := ('QO[_]_S) : type_scope.
Notation "''QO_' ( S )" := ('QO_S) (only parsing) : type_scope.
Notation "[ 'QO' 'of' f 'as' g ]" := (@clone _ _ f g _ idfun) : form_scope.
Notation "[ 'QO' 'of' f ]" := (@clone _ _ f _ _ id) : form_scope.
End Exports.

End QOperation.
Export QOperation.Exports.

(* quantum operation - complete positive trace preserving *)
Module QChannel.

Section ClassDef.
Variable (U V : chsType).
Notation axiom f := (f \is isqc).
Structure type := Pack { sort: 'SO(U,V); _ : axiom sort; }.
Local Coercion sort : type >-> superop.

Variables (T : 'SO(U,V)) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom (cT' : 'SO)) in c.
Definition clone c of phant_id class c := @Pack T c.

Local Canonical subType := Eval hnf in [subType for sort].
Definition eqMixin := Eval hnf in [eqMixin of type by <:].
Local Canonical  eqType  := Eval hnf in EqType type eqMixin.
Definition choiceMixin := [choiceMixin of type by <:].
Local Canonical  choiceType  := Eval hnf in ChoiceType type choiceMixin.
Definition porderMixin := [porderMixin of type by <:].
Local Canonical porderType :=
  Eval hnf in POrderType vorder_display type porderMixin.
Definition cpType := CPMap.Pack (isqc_cp class).
Definition qoType := QOperation.Pack (isqc_qo class).

End ClassDef.

Module Import Exports.
Coercion sort : type >-> superop.
Canonical subType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical cpType.
Canonical qoType.
Notation QCType M := (@Pack _ _ _ M).
Notation "''QC' ( S , T )" := (@type S T) : type_scope.
Notation "''QC' ( S )" := ('QC(S,S)) : type_scope.
Notation "''QC'" := ('QC(_,_)) (only parsing) : type_scope.
Notation "''QC[' H ]_ ( S , T )" := ('QC('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''QC[' H ]_ S" := ('QC[H]_(S,S))   (only parsing) : type_scope.
Notation "''QC[' H ]_ ( S )" := ('QC[H]_S)    (only parsing) : type_scope.
Notation "''QC_' ( S , T )"  := ('QC[_]_(S,T)) : type_scope.
Notation "''QC_' S"  := ('QC[_]_S) : type_scope.
Notation "''QC_' ( S )" := ('QC_S) (only parsing) : type_scope.
Notation "[ 'QC' 'of' f 'as' g ]" := (@clone _ _ f g _ idfun) : form_scope.
Notation "[ 'QC' 'of' f ]" := (@clone _ _ f _ _ id) : form_scope.
End Exports.

End QChannel.
Export QChannel.Exports.

Section KrausOp.
Variable (U V : chsType).

Lemma tn_tnE (F : finType) (f : F -> 'Hom(U,V)) (tn : trace_nincr f) :
  f = TNType tn.
Proof. by []. Qed.

Lemma tp_qmE (F : finType) (f : F -> 'Hom(U,V)) (tp : trace_presv f) :
  f = QMType tp.
Proof. by []. Qed.

Lemma cp_cpE (E : 'SO(U,V)) (cp : E \is iscp) : E = CPType cp.
Proof. by []. Qed.

Lemma qo_qoE (E : 'SO(U,V)) (qo : E \is isqo) : E = QOType qo.
Proof. by []. Qed.

Lemma qc_qcE (E : 'SO(U,V)) (qc : E \is isqc) : E = QCType qc.
Proof. by []. Qed.

Lemma trNincrP (F : finType) (A B : 'TN(F;U,V)) : A =1 B <-> A = B.
Proof.
split=>[|->//]; destruct A; destruct B=>/= /funext P1.
move: i0; rewrite -P1=>i0; by rewrite (Prop_irrelevance i i0).
Qed.

Lemma qmeasureP (F : finType) (A B : 'QM(F;U,V)) : A =1 B <-> A = B.
Proof.
split=>[|->//]; destruct A; destruct B=>/= /funext P1.
move: i0; rewrite -P1=>i0; by rewrite (Prop_irrelevance i i0).
Qed.
Definition trPresvP := qmeasureP.

Lemma tn_tnP (F : finType) (A : 'TN(F;U,V)) : trace_nincr A.
Proof. by destruct A. Qed.

Lemma qm_tpP (F : finType) (A : 'QM(F;U,V)) : trace_presv A.
Proof. by destruct A. Qed.
Definition tp_tpP := qm_tpP.

Lemma qm_tpE (F : finType) (A : 'QM(F;U,V)) : \sum_i ((A i)^A \o A i) = \1.
Proof. apply/eqP/qm_tpP. Qed.
Definition tp_tpE := qm_tpE.

Lemma tn_trlf_psd (F : finType) (A : 'TN(F;U,V)) x :
  x \is psdlf -> \sum_i \Tr (A i \o x \o (A i)^A) <= \Tr x.
Proof.
under eq_bigr do rewrite lftraceC comp_lfunA.
rewrite -linear_sum/= -linear_suml/= -{3}(comp_lfun1l x).
apply/lef_psdtr/tn_tnP.
Qed.

Lemma qm_trlf (F : finType) (A : 'QM(F;U,V)) x :
  \sum_i \Tr (A i \o x \o (A i)^A) = \Tr x.
Proof. 
under eq_bigr do rewrite lftraceC comp_lfunA.
by rewrite -linear_sum/= -linear_suml/= tp_tpE comp_lfun1l.
Qed.
Definition tp_trlf := qm_trlf.

Lemma cp_iscpP (x : 'CP(U,V)) : (x : 'SO) \is iscp.
Proof. by destruct x. Qed.

Lemma qo_isqoP (x : 'QO(U,V)) : (x : 'SO) \is isqo.
Proof. by destruct x. Qed.

Lemma qc_isqcP (x : 'QC(U,V)) : (x : 'SO) \is isqc.
Proof. by destruct x. Qed.

Lemma krausso_cp (F : finType) (f : F -> 'Hom(U,V)) :
  krausso f \is iscp.
Proof. apply/iscpP; exact: krausso2choi_psd. Qed.
Canonical krausso_cpType F f := CPType (@krausso_cp F f).

Lemma formso_cp (f : 'Hom(U,V)) : 
  formso f \is iscp.
Proof. apply: krausso_cp. Qed.
Canonical formso_cpType f := CPType (@formso_cp f).

Lemma krausso_qoP (F : finType) (f : F -> 'Hom(U,V)) :
  trace_nincr f <-> krausso f \is isqo.
Proof.
rewrite krausso2choi_trace_nincr; split=>[P1|/isqoP [_//]].
apply/isqoP; split=>//; exact: krausso2choi_psd.
Qed.
Lemma krausso_qo (F : finType) (f : 'TN(F;U,V)) :
  krausso f \is isqo.
Proof. apply/krausso_qoP/tn_tnP. Qed.
Canonical krausso_qoType F f := QOType (@krausso_qo F f).

Lemma krausso_qcP (F : finType) (f : F -> 'Hom(U,V)) :
  trace_presv f <-> krausso f \is isqc.
Proof.
rewrite krausso2choi_trace_presv; split=>[P1|/isqcP [_//]].
apply/isqcP; split=>//; exact: krausso2choi_psd.
Qed.
Lemma krausso_qc (F : finType) (f : 'QM(F;U,V)) :
  krausso f \is isqc.
Proof. apply/krausso_qcP/tp_tpP. Qed.
Canonical krausso_qcType F f := QCType (@krausso_qc F f).

Definition krausop (x : 'SO(U,V)) := choi2kraus (so2choi x).
Lemma krausopE (x : 'CP(U,V)) : x = krausso (krausop x) :> 'SO.
Proof. rewrite /krausop krausso2choiK//; apply: iscpP; apply/cp_iscpP. Qed.

Lemma krausE (E : 'CP(U,V)) x :
  E x = \sum_i ((@krausop E i) \o x \o (@krausop E i)^A)%VF.
Proof. by rewrite {1}krausopE kraussoE. Qed.

Lemma krausop_tn (x : 'QO(U,V)) : trace_nincr (krausop x).
Proof. by rewrite -choi2kraus_trace_nincr; move: (qo_isqoP x)=>/isqoP[?//]. Qed.
Canonical krausop_tnType x := TNType (@krausop_tn x).

Lemma krausop_tp (x : 'QC(U,V)) : trace_presv (krausop x).
Proof. by rewrite -choi2kraus_trace_presv; move: (qc_isqcP x)=>/isqcP[?//]. Qed.
Canonical krausop_tpType x := TPType (@krausop_tp x).

Lemma cp_isqcP (E: 'CP(U,V)) : 
  reflect (forall x, \Tr (E x) = \Tr x) ((E : 'SO) \is isqc).
Proof.
rewrite qualifE. apply/(iffP andP)=>[[P1 P2] x|P].
rewrite krausE linear_sum/=. under eq_bigr do rewrite lftraceC comp_lfunA.
rewrite -linear_sum/= -linear_suml/=.
move: (esym (choi2kraus_trace_presv P1)); rewrite P2=>/eqP->.
by rewrite comp_lfun1l.
move: (cp_iscpP E)=>/iscpP P1. split=>//.
rewrite choi2kraus_trace_presv//.
apply/trlf_introl=>x; rewrite linear_sumr linear_sum/=.
under eq_bigr do rewrite comp_lfunA lftraceC comp_lfunA.
by rewrite -linear_sum/= -krausE P comp_lfun1r.
Qed.

Lemma cp_isqoP (E : 'CP(U,V)) :
  reflect (forall x, x \is psdlf -> \Tr (E x) <= \Tr x) ((E : 'SO) \is isqo).
Proof.
rewrite qualifE. apply/(iffP andP)=>[[P1 P2] x|P].
rewrite krausE linear_sum/=. under eq_bigr do rewrite lftraceC comp_lfunA.
rewrite -linear_sum/= -linear_suml/= -{3}(comp_lfun1l x).
apply: lef_psdtr.
by move: (esym (choi2kraus_trace_nincr P1)); rewrite P2.
move: (cp_iscpP E)=>/iscpP P1. split=>//.
rewrite choi2kraus_trace_nincr//.
apply/lef_psdtr=>x Px.
rewrite linear_suml linear_sum/=.
under eq_bigr do rewrite -comp_lfunA lftraceC.
by rewrite -linear_sum/= -krausE comp_lfun1l P.
Qed.

Lemma qc_trlfE (E: 'QC(U,V)) x : \Tr (E x) = \Tr x.
Proof. apply/cp_isqcP/qc_isqcP. Qed.

Lemma qo_trlfE (E: 'QO(U,V)) x : x \is psdlf -> \Tr (E x) <= \Tr x.
Proof. apply/cp_isqoP/qo_isqoP. Qed.

Lemma cp_psdP (E : 'CP(U,V)) x : x \is psdlf -> (E x) \is psdlf.
Proof.
rewrite !psdlfE=>P1.
by rewrite krausE/= sumv_ge0// =>i _; apply/gef0_formV.
Qed.

End KrausOp.

Section QOConstruct.
Implicit Type (U V W : chsType).

(* abortso is cp, qo *)
Lemma abortso_formE U V : (0 : 'SO) = formso (0 : 'Hom(U,V)).
Proof. by apply/superopP=>x; rewrite !soE !comp_lfun0l. Qed.
Lemma abortso_cp U V : (0 : 'SO(U,V)) \is iscp.
Proof. by rewrite abortso_formE cp_iscpP. Qed.
Canonical abortso_cpType U V := CPType (@abortso_cp U V).
Lemma abortso_qo U V : (0 : 'SO(U,V)) \is isqo.
Proof. by apply/cp_isqoP=>x /psdlf_trlf; rewrite /= soE linear0. Qed.
Canonical abortso_qoType U V := QOType (@abortso_qo U V).

(* idso is cp, qo, qc *)
Lemma idso_formE U : :1 = formso (\1 : 'End(U)).
Proof. by apply/superopP=>x; rewrite !soE adjf1 comp_lfun1l comp_lfun1r. Qed.
Lemma idso_cp U : (:1 : 'SO(U)) \is iscp.
Proof. by rewrite idso_formE cp_iscpP. Qed.
Canonical idso_cpType U := CPType (@idso_cp U).
Lemma idso_qc U : (:1 : 'SO(U)) \is isqc.
Proof. by apply/cp_isqcP=>x; rewrite /= soE. Qed.
Canonical idso_qcType U := QCType (@idso_qc U).
Lemma idso_qo U : (:1 : 'SO(U)) \is isqo.
Proof. apply/isqc_qo/qc_isqcP. Qed.
Canonical idso_qoType U := QOType (@idso_qo U).

(* unitaryso is cp, qo, qc *)
Definition unitaryso U (f: 'FU(U)) := formso f.
Canonical unitaryso_cpType U f := 
  Eval hnf in [CP of (@unitaryso U f) as [CP of (@unitaryso U f)]].
Lemma unitaryso_qc U f : (@unitaryso U f) \is isqc.
Proof. by apply/cp_isqcP=>x; rewrite /= soE lftraceC comp_lfunA unitaryf_form comp_lfun1l. Qed.
Canonical unitaryso_qcType U f := QCType (@unitaryso_qc U f).
Lemma unitaryso_qo U f : (@unitaryso U f) \is isqo.
Proof. apply/isqc_qo/qc_isqcP. Qed.
Canonical unitaryso_qoType U f := QOType (@unitaryso_qo U f).

Definition unitarysoE := formsoE.
Lemma unitaryso1 (U : chsType) : unitaryso [unitary of (\1 : 'End(U))] = :1.
Proof. by apply/superopP=>x; rewrite formsoE/= comp_lfun1l adjf1 comp_lfun1r soE. Qed.

(* initialso is cp, qo, qc *)
Definition initialso U (v : 'NS(U)) := krausso (fun i=>[> v ; eb i : U <]).
Canonical initialso_cpType U v := 
  Eval hnf in [CP of (@initialso U v) as [CP of (@initialso U v)]].
Lemma initialso_qc U v : (@initialso U v) \is isqc.
Proof.
apply/cp_isqcP=>x; rewrite /= soE linear_sum/=. 
under eq_bigr do rewrite lftraceC comp_lfunA adj_outp outp_comp ns_dot scale1r.
by rewrite -linear_sum/= -linear_suml/= sumonb_out comp_lfun1l.
Qed.
Canonical initialso_qcType U v := QCType (@initialso_qc U v).
Lemma initialso_qo U v : (@initialso U v) \is isqo.
Proof. apply/isqc_qo/qc_isqcP. Qed.
Canonical initialso_qoType U v := QOType (@initialso_qo U v).

Lemma initialsoE U (v : 'NS(U)) x : initialso v x = \Tr x *: [> v ; v <].
Proof.
rewrite soE (onb_trlf eb_onbasis x)/= scaler_suml; apply eq_bigr=>i _.
by rewrite adj_outp -comp_lfunA outp_compr outp_comp.
Qed.

Lemma initialso_onb U (v : 'NS(U)) (F : finType) (onb : 'ONB(F;U)) :
  krausso (fun i=>[> v ; onb i <]) = initialso v.
Proof.
apply/superopP=>x; rewrite soE initialsoE (onb_trlf onb x)/= scaler_suml.
by apply eq_bigr=>i _; rewrite adj_outp -comp_lfunA outp_compr outp_comp.
Qed.


(* ifso, cp - cp, qo - qo, qc - qc *)
Lemma ifso_cp U V W (F : finType) (f : F -> 'Hom(U, V)) (br : F -> 'CP(V, W)) :
  ifso f br \is iscp.
Proof.
have ->: (fun x : F => br x : 'SO) = (fun x : F => krausso (krausop (br x))).
apply/funext=>i; exact: krausopE. 
by rewrite ifso_krausso cp_iscpP.
Qed.
Canonical ifso_cpType U V W F f br := CPType (@ifso_cp U V W F f br).

Lemma ifso_qo U V W (F : finType) (f : 'TN(F;U,V)) (br : F -> 'QO(V, W)) :
  ifso f br \is isqo.
Proof.
apply/cp_isqoP=>x Px; apply: (le_trans _ (tn_trlf_psd f Px)).
rewrite ifsoE linear_sum/= ler_sum// =>i _.
apply/qo_trlfE; move: Px; rewrite !psdlfE; exact: gef0_formV.
Qed.
Canonical ifso_qoType U V W F f br := QOType (@ifso_qo U V W F f br).

Lemma ifso_qc U V W (F : finType) (f : 'QM(F;U,V)) (br : F -> 'QC(V, W)) :
  ifso f br \is isqc.
Proof.
apply/cp_isqcP=>x; rewrite -[RHS](tp_trlf f) ifsoE linear_sum/=.
apply eq_bigr =>i _; apply/qc_trlfE.
Qed.
Canonical ifso_qcType U V W F f br := QCType (@ifso_qc U V W F f br).

(* comp_so, cp - cp, qo - qo, qc - qc *)
Lemma comp_so_cp U V W (E: 'CP(U,V)) (F: 'CP(W,U)) :
  E :o F \is iscp.
Proof. by rewrite krausopE (krausopE F) comp_krausso cp_iscpP. Qed.
Canonical comp_so_cpType U V W E F := CPType (@comp_so_cp U V W E F).
Lemma comp_so_qo U V W (E: 'QO(U,V)) (F: 'QO(W,U)) :
  E :o F \is isqo.
Proof.
apply/cp_isqoP=>x Px; apply: (le_trans _ (qo_trlfE F Px)). 
by rewrite comp_soE qo_trlfE// cp_psdP.
Qed.
Canonical comp_so_qoType U V W E F := QOType (@comp_so_qo U V W E F).
Lemma comp_so_qc U V W (E: 'QC(U,V)) (F: 'QC(W,U)) :
  E :o F \is isqc.
Proof. by apply/cp_isqcP=>x; rewrite comp_soE !qc_trlfE. Qed.
Canonical comp_so_qcType U V W E F := QCType (@comp_so_qc U V W E F).

Lemma comp_sor_cp U V W (E: 'CP(U,V)) (F: 'CP(V,W)) :
  E o: F \is iscp.
Proof. by rewrite comp_soErl cp_iscpP. Qed.
Canonical comp_sor_cpType U V W E F := CPType (@comp_sor_cp U V W E F).
Lemma comp_sor_qo U V W (E: 'QO(U,V)) (F: 'QO(V,W)) :
  E o: F \is isqo.
Proof. by rewrite comp_soErl qo_isqoP. Qed.
Canonical comp_sor_qoType U V W E F := QOType (@comp_sor_qo U V W E F).
Lemma comp_sor_qc U V W (E: 'QC(U,V)) (F: 'QC(V,W)) :
  E o: F \is isqc.
Proof. by rewrite comp_soErl qc_isqcP. Qed.
Canonical comp_sor_qcType U V W E F := QCType (@comp_sor_qc U V W E F).

(* dualso property cp - cp *)
Lemma dualso_cp U V (E : 'CP(U,V)) : dualso E \is iscp.
Proof. by rewrite krausopE dualso_krausso cp_iscpP. Qed.
Canonical dualso_cpType U V E := CPType (@dualso_cp U V E).

Lemma dualso_comp U V W (E : 'SO(U,V)) (F : 'SO(W,U)) :
  dualso (E :o F) = dualso F :o dualso E.
Proof.
apply/superopP=>A; apply/eqP/trlf_introl=>x.
by rewrite comp_soE -!dualso_trlfE comp_soE.
Qed.

Lemma dualso_compr U V W (E : 'SO(U,V)) (F : 'SO(V,W)) :
  dualso (E o: F) = dualso F o: dualso E.
Proof.
apply/superopP=>A; apply/eqP/trlf_introl=>x.
by rewrite comp_sorE -!dualso_trlfE comp_sorE.
Qed.

Lemma dualso_unitary U (f : 'FU(U)) : 
  dualso (unitaryso f) = unitaryso ([unitary of f^A]).
Proof. by rewrite /unitaryso dualso_formso. Qed.

Lemma dualso_initialE U (v : 'NS(U)) (x : 'End(U)) :
  dualso (initialso v) x = [<v : U ; x (v : U)>] *: \1.
Proof.
rewrite /initialso dualso_krausE.
under eq_bigr do rewrite adj_outp outp_compl outp_comp -adj_dotE.
by rewrite -linear_sum/= sumonb_out.
Qed.

Lemma dualso0 U V : dualso (0: 'SO(U,V)) = 0.
Proof. by rewrite abortso_formE dualso_formso linear0 -abortso_formE. Qed.
Lemma dualso1 U : dualso (:1 : 'SO(U)) = :1.
Proof. by rewrite idso_formE dualso_formso adjf1. Qed.

(* part of tn / qm *)
Lemma tn_elem_tn U V (F : finType) (f : 'TN(F;U,V)) (i : F) :
  (f i)^A \o (f i) ⊑ \1.
Proof.
apply: (le_trans _ (tn_tnP f)); rewrite (bigD1 i)//= lev_addl sumv_ge0// =>j _;
by rewrite form_ge0.
Qed.
Definition elemso U V (F : finType) (f : F -> 'Hom(U,V)) (i : F) := formso (f i).
Canonical elemso_cpType U V F f i := Eval hnf in [CP of (@elemso U V F f i)].
Lemma elemso_qo U V (F : finType) (f : 'TN(F;U,V)) i : (@elemso U V F f i) \is isqo.
Proof. 
apply/cp_isqoP=>x. rewrite soE lftraceC comp_lfunA -{3}(comp_lfun1l x).
apply/lef_psdtr/tn_elem_tn.
Qed.
Canonical elemso_qoType U V F f i := QOType (@elemso_qo U V F f i).

Lemma elemso_sum U V (F : finType) (f : F -> 'Hom(U,V)) :
  \sum_i (elemso f i) = krausso f.
Proof. by apply/superopP=>x; rewrite !soE; under eq_bigr do rewrite soE. Qed.

Lemma ifso_elemE U V W (F : finType) (f : F -> 'Hom(U,V)) (br : F -> 'SO(V, W)) x:
  ifso f br x = \sum_i ((br i :o elemso f i) x).
Proof. by under eq_bigr do rewrite comp_soE soE; rewrite ifsoE. Qed.

Lemma ifso_elem U V W (F : finType) (f : F -> 'Hom(U,V)) (br : F -> 'SO(V, W)):
  ifso f br = \sum_i (br i :o elemso f i).
Proof. by apply/superopP=>x; rewrite !soE ifso_elemE. Qed.

Lemma elemso_trlf U V (F : finType) (f : 'QM(F;U,V)) x :
  \sum_i \Tr ((elemso f i) x) = \Tr x.
Proof. under eq_bigr do rewrite soE; exact: qm_trlf. Qed.

Lemma dualso_if U V W (F : finType) (f : F -> 'Hom(U,V)) (br : F -> 'SO(V, W)) :
  dualso (ifso f br) = \sum_i dualso (br i :o (elemso f i)).
Proof. by rewrite ifso_elem linear_sum. Qed.

Definition dualqm U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) :=
  \sum_i ((f i)^A \o (O i) \o (f i)).

Lemma dualqmE U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) :
  dualqm f O = \sum_i ((elemso f i)^*o (O i)).
Proof. by under eq_bigr do rewrite dualso_formE. Qed.

Lemma dualqm_trlfE U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) (x : 'End(U)) :
  \sum_i \Tr ((elemso f i) x \o O i) = \Tr (x \o dualqm f O).
Proof.
rewrite /dualqm linear_sumr linear_sum. apply eq_bigr=>i _.
by rewrite dualso_trlfE dualso_formE.
Qed.

Lemma dualqm_trlfEV U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) (x : 'End(U)) :
  \sum_i \Tr (O i \o (elemso f i) x) = \Tr (dualqm f O \o x).
Proof. by under eq_bigr do rewrite lftraceC; rewrite dualqm_trlfE lftraceC. Qed.

Lemma bool_index : index_enum bool_finType = [:: true; false].
Proof. by rewrite /index_enum !unlock/=. Qed.

Lemma ifso_boolE U V W (M : bool -> 'Hom(U,V))
  (br : forall (b : bool), 'SO(V,W)) b x :
  ifso M br x = (br b :o elemso M b) x + (br (~~b) :o elemso M (~~b)) x.
Proof.
rewrite ifso_elemE bool_index unlock/= /reducebig/= addr0.
by case: b=>[//|]; rewrite addrC.
Qed.
Global Arguments ifso_boolE [U V W M br].

Lemma ifso_bool U V W (M : bool -> 'Hom(U,V))
  (br : forall (b : bool), 'SO(V,W)) b :
  ifso M br = (br b :o elemso M b) + (br (~~b) :o elemso M (~~b)).
Proof. by apply/superopP=>x; rewrite soE -ifso_boolE. Qed.
Global Arguments ifso_bool [U V W M br].

Lemma abortso_eq0 U V : (@abortso U V) = 0.
Proof. by []. Qed.

Lemma addso_cp U V (E F : 'CP(U,V)) : (E : 'SO) + F \is iscp.
Proof. by rewrite krausopE (krausopE F) addso_krausso cp_iscpP. Qed.
Canonical addso_cpType U V E F := CPType (@addso_cp U V E F).

Lemma sumso_cp U V F (r : seq F) (P : pred F) (f : F -> 'CP(U,V)) :
  \sum_(i <- r | P i) (f i : 'SO) \is iscp.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil cp_iscpP.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (cp_cpE IH) cp_iscpP.
Qed.

Lemma complso_cp U F (r : seq F) (P : pred F) (f : F -> 'CP(U)) :
  \compl_(i <- r | P i) (f i : 'SO) \is iscp.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil cp_iscpP.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (cp_cpE IH) cp_iscpP.
Qed.

Lemma complso_qo U F (r : seq F) (P : pred F) (f : F -> 'QO(U)) :
  \compl_(i <- r | P i) (f i : 'SO) \is isqo.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil qo_isqoP.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (qo_qoE IH) qo_isqoP.
Qed.

Lemma complso_qc U F (r : seq F) (P : pred F) (f : F -> 'QC(U)) :
  \compl_(i <- r | P i) (f i : 'SO) \is isqc.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil qc_isqcP.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (qc_qcE IH) qc_isqcP.
Qed.

Lemma comprso_cp U F (r : seq F) (P : pred F) (f : F -> 'CP(U)) :
  \compr_(i <- r | P i) (f i : 'SO) \is iscp.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil cp_iscpP.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (cp_cpE IH) cp_iscpP.
Qed.

Lemma comprso_qo U F (r : seq F) (P : pred F) (f : F -> 'QO(U)) :
  \compr_(i <- r | P i) (f i : 'SO) \is isqo.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil qo_isqoP.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (qo_qoE IH) qo_isqoP.
Qed.

Lemma comprso_qc U F (r : seq F) (P : pred F) (f : F -> 'QC(U)) :
  \compr_(i <- r | P i) (f i : 'SO) \is isqc.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil qc_isqcP.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (qc_qcE IH) qc_isqcP.
Qed.

End QOConstruct.

Canonical comp_so_monoid (U : chsType) := Monoid.Law (@comp_soA U U U U) (@comp_so1l U U) (@comp_so1r U U).
Canonical comp_sor_monoid (U : chsType) := Monoid.Law (@comp_sorA U U U U) (@comp_sor1l U U) (@comp_sor1r U U).

Section QOQMDenObs.
Implicit Type (U V: chsType).

Lemma cp_ge0 U V (E: 'CP(U,V)) (x:'End(U)) :
  (0 : 'End(U)) ⊑ x -> (0 : 'End(V)) ⊑ E x.
Proof. rewrite -!psdlfE; exact: cp_psdP. Qed.

Lemma cp_preserve_order U V (E: 'CP(U,V)) (x y:'End(U)) :
  x ⊑ y -> E x ⊑ E y.
Proof. by rewrite -subv_ge0=>/(cp_ge0 E); rewrite linearB/= subv_ge0. Qed.

Lemma qo_dualP U V (E: 'CP(U,V)) : 
  reflect (E^*o \1 ⊑ \1) ((E : 'SO) \is isqo).
Proof.
rewrite {1}krausopE dualsoE; under eq_bigr do rewrite comp_lfun1r.
apply/(iffP idP)=>P. rewrite (qo_qoE P). exact: krausop_tn.
by rewrite krausopE (tn_tnE P) qo_isqoP.
Qed.

Lemma dual_qo1_le1 U V (E: 'QO(U,V)) : E^*o \1 ⊑ \1.
Proof. apply/qo_dualP/qo_isqoP. Qed.

Lemma qc_dualP U V (E: 'CP(U,V)) : 
  reflect (E^*o \1 = \1) ((E : 'SO) \is isqc).
Proof.
rewrite {1}krausopE dualsoE; under eq_bigr do rewrite comp_lfun1r.
apply/(iffP idP)=>[P|/eqP P]. rewrite (qc_qcE P); apply/eqP/krausop_tp.
by rewrite krausopE (tp_qmE P) qc_isqcP.
Qed.

Lemma dual_qc1_eq1 U V (E: 'QC(U,V)) : E^*o \1 = \1.
Proof. by apply/qc_dualP/qc_isqcP. Qed.

Lemma cp_psdlf U V (E : 'CP(U,V)) (x : 'F+(U)) : E x \is psdlf.
Proof. apply/cp_psdP/psdf_psd. Qed.
Canonical cp_psdfType U V E x := PsdfType (@cp_psdlf U V E x).

Lemma qo_denlf U V (E : 'QO(U,V)) (x : 'FD(U)) : E x \is denlf.
Proof.
apply/denlfP; split. apply/cp_psdP/denlf_psd/denf_den.
apply: (le_trans _ (denf_trlf x)); apply/qo_trlfE/denlf_psd/denf_den.
Qed.
Canonical qo_denfType U V E x := DenfType (@qo_denlf U V E x).

(* Lemma qc_den1lf U V (E : 'QC(U,V)) (x : 'FD1(U)) : E x \is den1lf. *)

Lemma dualqo_obslf U V (E : 'QO(U,V)) (O : 'FO(V)) : E^*o O \is obslf.
Proof.
move: (obsf_ge0 O) (obsf_le1 O)=>P1 P2.
rewrite lef_obs. apply/andP. split.
by apply/cp_ge0. apply: (le_trans _ (dual_qo1_le1 E)).
by apply/cp_preserve_order.
Qed.
Canonical dualqo_obsfType U V E O := ObsfType (@dualqo_obslf U V E O).

Lemma dualqm_obslf U V (F: finType) (M : 'TN(F;U,V)) (Of : F -> 'FO(V)) :
  dualqm M Of \is obslf.
Proof.
rewrite lef_obs. apply/andP. split.
by rewrite sumv_ge0// =>i _; rewrite gef0_form// obsf_ge0.
apply: (le_trans _ (dual_qo1_le1 [QO of krausso M])).
rewrite dualqmE/= -elemso_sum linear_sum/= soE lev_sum// =>i _.
apply/cp_preserve_order/obsf_le1.
Qed.
Canonical dualqm_obsfType U V F M O := ObsfType (@dualqm_obslf U V F M O).

Lemma elem_sum_trlfE U V (F: finType) (M : 'QM(F;U,V)) x :
  \sum_i \Tr (elemso M i x) = \Tr x.
Proof. by rewrite -linear_sum/= -sum_soE elemso_sum qc_trlfE. Qed.

Lemma cpgeso0 (U V: chsType) (E: 'CP(U,V)) : (0 : 'SO) ⊑ E.
Proof. by rewrite leso_mx linear0 le_lownerE subr0; apply: iscpP; apply/cp_iscpP. Qed.

Lemma cpge0 (U V: chsType) (E: 'CP(U,V)) : [CP of 0] ⊑ E.
Proof. by rewrite leEsub/= cpgeso0. Qed.

Lemma qoge0 (U V: chsType) (E: 'QO(U,V)) : [QO of 0] ⊑ E.
Proof. by rewrite leEsub/= cpgeso0. Qed.

Lemma scalemx_le m (a b: C) : a <= b -> (a%:M : 'M_m) ⊑ b%:M.
Proof.
move=>P1; rewrite le_lownerE; apply/psdmx_dot=>u.
rewrite mulmxBr !mul_mx_scalar -scalerBl -scalemxAl linearZ/= nnegrE.
apply mulr_ge0. by rewrite subr_ge0. by rewrite form_tr_ge0.
Qed.

Lemma qoubso (U V: chsType) (E: 'QO(U,V)) : 
  (E : 'SO) ⊑ (choi2so (Vector.dim U)%:R%:M)%VF.
Proof.
move: (qo_isqoP E)=>/isqoP[P1 P2].
rewrite /= leso_mx choi2soK; apply (le_trans (lemx_psd_ub P1)).
apply/scalemx_le; rewrite tr_ptrace; move: P2=>/lemx_trace P2.
by apply (le_trans P2); rewrite mxtrace_scalar muln1.
Qed.

Lemma leso0_cpP (U V: chsType) (E : 'SO(U,V)) :
  reflect ((0 : 'SO) ⊑ E) (E \is iscp).
Proof.
apply/(iffP (@iscpP _ _ _));
by rewrite leso_mx linear0 le_lownerE subr0.
Qed.

Lemma lecpP (U V: chsType) (E F : 'CP(U,V)) :
  reflect (exists W : 'CP(U,V), (W : 'SO) + E = F) (E ⊑ F).
Proof.
apply/(iffP idP)=>[|[W PW]].
rewrite leEsub leso_mx le_lownerE -linearB/==>P.
have P1: (F : 'SO(U,V)) - (E : 'SO(U,V)) \is iscp by apply/iscpP.
by exists (CPType P1); rewrite /= addrNK.
rewrite leEsub/= -PW leso_mx le_lownerE -linearB addrK/=.
by move: (cp_iscpP W)=>/iscpP.
Qed.

Lemma leqoP (U V: chsType) (E F : 'QO(U,V)) :
  reflect (exists W : 'QO(U,V), (W : 'SO) + E = F) (E ⊑ F).
Proof.
apply/(iffP idP)=>[|[W PW]].
rewrite leEsub leso_mx le_lownerE -linearB/==>P.
have P1: (F : 'SO(U,V)) - (E : 'SO(U,V)) \is isqo.
apply/isqoP; split=>//. rewrite !linearB/= le_lownerE opprB addrC -addrA.
apply/psdmx_add. apply/ptrace_psd. by move: (qo_isqoP E)=>/isqoP[->].
rewrite addrC -le_lownerE. by move: (qo_isqoP F)=>/isqoP[_->].
by exists (QOType P1); rewrite /= addrNK.
rewrite leEsub/= -PW leso_mx le_lownerE -linearB addrK/=.
by move: (qo_isqoP W)=>/isqoP[->].
Qed.

Lemma leso_preserve_order (U V: chsType) (E F : 'SO(U,V)) x:
  E ⊑ F -> (0 : 'End(U)) ⊑ x -> E x ⊑ F x.
Proof.
rewrite -subv_ge0=>/leso0_cpP P1.
rewrite -[in X in _ -> X]subv_ge0 -opp_soE -add_soE (cp_cpE P1).
exact: cp_ge0.
Qed.

End QOQMDenObs.

Module QOCPO.

Section QOCPOProof.
Local Close Scope lfun_scope.
Variable (U V: chsType).
Import HermitianTopology.Exports HermitianTopology.Theory HermitianTopology.
Local Open Scope classical_set_scope.

Local Notation qosort := (@QOperation.sort U V).

Definition qolub (u : nat -> 'QO(U,V)) :=
  match lim (qosort \o u) \is isqo =P true with
  | ReflectT is_qo => QOType is_qo
  | _ => [QO of 0]
  end.

Lemma chainqomap (u: nat -> 'QO(U,V)) :
  chain u -> nondecreasing_seq (qosort \o u).
Proof. by move=>/chain_homo P m n Pmn; move: (P _ _ Pmn). Qed.

Lemma chainqo_lb (u : nat -> 'QO(U,V)) : lbounded_by (0:'SO(U,V)) (qosort \o u).
Proof.
move=>i. rewrite leso_mx linear0/= le_lownerE subr0. 
by move: (qo_isqoP (u i))=>/isqoP[->].
Qed.

Lemma chainqo_ub (u : nat -> 'QO(U,V)) : 
  ubounded_by (choi2so (Vector.dim U)%:R%:M)%VF (qosort \o u).
Proof. move=>i/=; apply qoubso. Qed.

Lemma lim_qo (u : nat -> 'QO(U,V)) : 
  cvg (qosort \o u) -> [set x : 'SO(U,V) | x \is isqo] (lim (qosort \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (qosort \o u) _ _ _ _)=>//.
apply closed_isqo. by apply: nearW=>x/=; apply qo_isqoP.
Qed.

Lemma chainqo_cvg : forall c : nat -> 'QO(U,V), chain c ->
  cvg (qosort \o c).
Proof.
move=>c Pc. move: (chainqomap Pc) (chainqo_ub c)=>P1 P2.
by apply (vnondecreasing_is_cvg P1 P2).
Qed.

Lemma qolub_lub : forall c : nat -> 'QO(U,V), chain c -> (forall i, c i ⊑ qolub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> qolub c ⊑ x).
Proof.
move=>c Pc. move: (chainqomap Pc) (chainqo_cvg Pc)=>P1 P3.
move: (nondecreasing_cvg_lev P1 P3)=>P4.
rewrite /qolub; case: eqP=>P5; last by exfalso; apply P5; apply lim_qo.
split. by move=>i; rewrite leEsub/= P4.
move=>x Px. rewrite leEsub/=.
by apply: (@lim_lev _ _ (qosort x) _ P3)=>i; move: (Px i).
Qed.

Lemma qolub_ub : forall c : nat -> 'QO(U,V), chain c -> (forall i, c i ⊑ qolub c).
Proof. by move=>c /qolub_lub=>[[P1]]. Qed.

Lemma qolub_least : forall c : nat -> 'QO(U,V), 
  chain c -> forall x, (forall i, c i ⊑ x) -> qolub c ⊑ x.
Proof. by move=>c /qolub_lub=>[[_ ]]. Qed.

Import CpoMixin.Exports.
Definition qo_cpoMixin := CpoMixin (@qoge0 U V) qolub_ub qolub_least.
Local Canonical qo_cpoType := CpoType 'QO(U,V) qo_cpoMixin.

Lemma qolubE : forall c : nat -> 'QO(U,V), 
  chain c -> lim (qosort \o c)%FUN = lub c.
Proof.
move=>c Pc. rewrite /lub/= /qolub. case: eqP=>//.
by move: (chainqo_cvg Pc)=>/lim_qo/= ->.
Qed.

End QOCPOProof.

Module Import Exports.
Canonical qo_cpoType.
End Exports.
End QOCPO.
Export QOCPO.Exports.

Section QOWhile.
Import QOCPO HermitianTopology HermitianTopology.Exports HermitianTopology.Theory.
Variable (U: chsType).
Local Open Scope lfun_scope.

Fixpoint whileso_iter (M: bool -> 'End(U)) (b : bool) (D: 'SO(U)) (n : nat) :=
  match n with
  | O => (0 : 'SO(U))
  | S n => ifso M (fun b' => if b' == b then (whileso_iter M b D n) :o D else :1)
  end.

Fixpoint whileso_incr (M: bool -> 'End(U)) (b : bool) (D: 'SO(U)) (n : nat) :=
  match n with
  | O => :1
  | S n => (whileso_incr M b D n) :o (D :o (elemso M b)) 
  end.

Lemma whileso_incrED (M: bool -> 'End(U)) b (D: 'SO(U)) n :
  (whileso_incr M b D n.+1) = (whileso_incr M b D n) :o (D :o (elemso M b)).
Proof. by []. Qed.

Lemma whileso_incrE (M: bool -> 'End(U)) b (D: 'SO(U)) n :
  (whileso_incr M b D n.+1) = (D :o (elemso M b)) :o (whileso_incr M b D n).
Proof.
elim: n=>[|n IH]. by rewrite /= comp_so1l comp_so1r.
by rewrite whileso_incrED {1}IH whileso_incrED !comp_soA.
Qed.

Lemma neqb (b : bool) : ~~ b == b = false.
Proof. by case: b. Qed.

Lemma whileso_iter_incrEx (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) x :
  whileso_iter M b D n x = (elemso M (~~b)) (\sum_(i < n) (whileso_incr M b D i x)).
Proof.
elim: n x=>[x|n IH x]; first by rewrite big_ord0 linear0 /= soE.
rewrite (ifso_boolE b) eqxx neqb -/whileso_iter !comp_soE soE big_ord_recl /= IH.
rewrite -linearD/= soE addrC. do 2 f_equal. 
apply eq_bigr=>i _. by rewrite !comp_soE.
Qed.

Lemma whileso_iter_incrE (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) :
  whileso_iter M b D n = (elemso M (~~b)) :o (\sum_(i < n) (whileso_incr M b D i)).
Proof. by apply/superopP=>x; rewrite soE sum_soE whileso_iter_incrEx. Qed.

Lemma whileso_iterEx (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) x :
  whileso_iter M b D n.+1 x = whileso_iter M b D n x + 
    ((elemso M (~~b)) :o (whileso_incr M b D n)) x.
Proof. by rewrite !whileso_iter_incrEx big_ord_recr/= linearD comp_soE. Qed.

Lemma whileso_iterE (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) :
  whileso_iter M b D n.+1 = whileso_iter M b D n + 
    ((elemso M (~~b)) :o (whileso_incr M b D n)).
Proof. by apply/superopP=>x; rewrite soE whileso_iterEx. Qed.

Definition whileso (M: bool -> 'End(U)) b (D: 'SO(U)) :=
  lim (whileso_iter M b D).

Lemma whilso_incr_cp (M: bool -> 'End(U)) b (D: 'CP(U)) (n : nat) :
  whileso_incr M b D n \is iscp.
Proof.
elim: n=>[|n IH]; first by rewrite /= cp_iscpP.
by rewrite whileso_incrE (cp_cpE IH) cp_iscpP.
Qed.
Canonical whilso_incr_cpType M b D n := CPType (@whilso_incr_cp M b D n).

Lemma whilso_incr_qo (M: 'TN(bool;U)) b (D: 'QO(U)) (n : nat) :
  whileso_incr M b D n \is isqo.
Proof.
elim: n=>[|n IH]; first by rewrite /= qo_isqoP.
by rewrite whileso_incrE (qo_qoE IH) qo_isqoP.
Qed.
Canonical whilso_incr_qoType M b D n := QOType (@whilso_incr_qo M b D n).

Lemma whileso_iter_cp (M: bool -> 'End(U)) b (D: 'CP(U)) (n : nat) :
  whileso_iter M b D n \is iscp.
Proof.
elim: n=>[|n IH]; first by rewrite /= cp_iscpP.
by rewrite whileso_iterE (cp_cpE IH) cp_iscpP.
Qed.
Canonical whileso_iter_cpType M b D n := CPType (@whileso_iter_cp M b D n).

(* match : makes canonical of ifso fails *)
Lemma whileso_iter_qo (M: 'TN(bool;U)) b (D: 'QO(U)) (n : nat) :
  whileso_iter M b D n \is isqo.
Proof.
elim: n=>[|n IH/=]; first by rewrite /= qo_isqoP.
suff ->: (fun b' => if b' == b then whileso_iter M b D n :o D else :1)
  = (fun b' => if b' == b then [QO of QOType IH :o D] else [QO of :1]).
apply: qo_isqoP. by apply/funext=>b'; case: eqP.
Qed.
Canonical whileso_iter_qoType M b D n := QOType (@whileso_iter_qo M b D n).

(* whileso_iter is nondecreasing *)
Lemma whileso_iter_chain (M: bool -> 'End(U)) b (D: 'CP(U)) : chain (whileso_iter M b D).
Proof. by rewrite /chain=>i; rewrite whileso_iterE lev_addl; apply/cpgeso0. Qed.

Lemma whileso_iter_homo (M: bool -> 'End(U)) b (D: 'CP(U)) : 
  nondecreasing_seq (whileso_iter M b D).
Proof. by apply/chain_homo/whileso_iter_chain. Qed.

Lemma whileso_iter_ub (M: 'TN(bool;U)) b (D: 'QO(U)) : 
  ubounded_by (choi2so (Vector.dim U)%:R%:M) (whileso_iter M b D).
Proof. by move=>i; apply/qoubso. Qed.

Lemma whileso_cvg (M: 'TN(bool;U)) b (D: 'QO(U)) : 
  (whileso_iter M b D --> whileso M b D)%classic.
Proof.
apply: (vnondecreasing_is_cvg (whileso_iter_homo _ b _) (whileso_iter_ub M b D)).
Qed.

Lemma whileso_qo (M: 'TN(bool;U)) b (D: 'QO(U)) :
  whileso M b D \is isqo.
Proof.
suff : [set x : 'SO(U) | x \is isqo]%classic (lim (whileso_iter M b D)) by [].
apply: (@closed_cvg _ _ _ eventually_filter (whileso_iter M b D) _ _ _ _)=>//.
apply closed_isqo. by apply: nearW=>x/=; apply qo_isqoP.
apply: whileso_cvg.
Qed.
Canonical whileso_qoType M b D := QOType (@whileso_qo M b D).
Lemma whileso_cp (M: 'TN(bool;U)) b (D: 'QO(U)) :
  whileso M b D \is iscp.
Proof. apply/isqo_cp/whileso_qo. Qed.
Canonical whileso_cpType M b D := CPType (@whileso_cp M b D).

Lemma whileso_ub (M: 'TN(bool;U)) b (D: 'QO(U)) i : whileso_iter M b D i ⊑ whileso M b D.
Proof.
apply: (nondecreasing_cvg_lev (whileso_iter_homo _ b _) (@whileso_cvg M b D)).
Qed.

Lemma whileso_least (M: 'TN(bool;U)) b (D: 'QO(U)) x :
  (forall i, whileso_iter M b D i ⊑ x) -> whileso M b D ⊑ x.
Proof. apply: (lim_lev (@whileso_cvg M b D)). Qed.

Lemma whileso_lim (M: bool -> 'End(U)) b (D: 'SO(U)) : 
  lim (whileso_iter M b D) = whileso M b D.
Proof. by []. Qed.

Lemma whileso_is_cvg (M: 'TN(bool;U)) b (D: 'QO(U)) : cvg (whileso_iter M b D).
Proof. apply/cvg_ex; exists (whileso M b D); apply whileso_cvg. Qed.

End QOWhile.

Section QOWhileRanking.
Import CTopology.Exports QOCPO.
Variable (U: chsType) (M: 'TN(bool;U)) (b: bool) (D: 'QO(U)).

Definition ranking_function (P: 'FO(U)) 
(t : C -> 'FD(U) -> nat) :=
  forall e, e > 0 ->
  (forall x : 'FD(U), (t e [den of (D :o elemso M b) x] <= t e x)%N /\
  (\Tr (P \o x) >= e -> (t e [den of (D :o elemso M b) x] < t e x)%N)).

Lemma trlfM_ge0 (V: chsType) (f: 'End(V)) (g: 'End(V)) :
  (0 : 'End(V)) ⊑ f -> (0 : 'End(V)) ⊑ g -> 0 <= \Tr (f \o g).
Proof.
move/ge0_form=>[f' ->]/ge0_form[g' ->].
rewrite comp_lfunA lftraceC. apply/psdlf_trlf.
by rewrite psdlfE -{2}(adjfK f') -comp_lfunA -adjf_comp comp_lfunA formV_ge0.
Qed.

Lemma nat_well_founded (tt : nat -> nat) : 
  (forall n : nat, (tt n.+1 < tt n)%N) -> False.
Proof.
move=>H.
have P n: (tt n >= 0 -> tt n <= tt 0 - n)%N.
elim: n=>[_|n IH]. by rewrite subn0.
move=>P1. move: (leq_ltn_trans P1 (H _))=> P3.
move: {+}P3=>/ltnW/IH P2. move: (leq_trans P3 P2)=>P4.
rewrite -(leq_add2r 1) addn1. apply (leq_trans (H _)).
apply (leq_trans P2).
rewrite -addn1 -subnA. by rewrite addn1. 
rewrite -leq_psubRL//. by rewrite addn1 subn1.
move: (leq0n (tt (tt 0%N)))=>/P. rewrite subnn leqn0=>/eqP P1.
move: (H (tt 0%N)). by rewrite P1.
Qed.

Fixpoint minpred (P : nat -> bool) m :=
  if (P m) then
    match m with
    | O => 0%N
    | S m' => (minpred P m')
    end
  else m.+1.

Lemma minpred0 (P : nat -> bool) m : ((minpred P m) <= m.+1)%N.
Proof.
elim: m=>[/=|n IH/=]. by case: (P 0%N).
case: (P n.+1)=>//. by apply (leq_trans IH).
Qed.

Lemma minpred6 (P : nat -> bool) m : P m -> ((minpred P m) <= m)%N.
Proof.
case: m=>/=. by move=>->.
move=>n ->. apply minpred0.
Qed.

Lemma minpred5 (P : nat -> bool) m n : ((minpred P m) <= n)%N -> (n <= m)%N -> P n.
Proof.
elim: m. rewrite /=leqn0=>+/eqP P1. rewrite P1; by case E: (P 0%N).
move=>m IH. rewrite /=. case E: (P m.+1).
rewrite [in X in _ -> X]leq_eqVlt. case: eqP=>[->//|_ P1/= P2].
by apply IH.
move=>P1 P2. move: (leq_ltn_trans P2 P1). by rewrite ltnn.
Qed.

Lemma nat_hausdorff : hausdorff_space [topologicalType of nat].
Proof.
rewrite /hausdorff_space/==>p q.
have P (k : nat) : nbhs k [set k]%classic. rewrite nbhsE/=.
exists ([set k]%classic). split=>//.
rewrite /open_nbhs /open/= /open_from/=. split=>//.
exists ([set k]%classic)=>//.
by rewrite predeqE => i/=; rewrite bigcup_set1/=.
by move=>/(_ [set p]%classic [set q]%classic (P p) (P q))[k/=][ <-<-].
Qed.

Lemma minpred4 (P : nat -> bool) m : 
  (forall n, (m <= n)%N -> P n) -> lim (minpred P) = minpred P m.
Proof.
move=>H.
suff: ((minpred P) --> (minpred P m))%classic.
by move/(cvg_lim nat_hausdorff)=>/=->.
rewrite -(cvg_shiftn m)/=.
have->: (fun n : nat => minpred P (n + m)) = (fun=>minpred P m).
apply/funext=>x. elim: x=>[|n IH]. by rewrite add0n.
by rewrite addSn/= H ?IH// leqW// leq_addl.
apply: cvg_cst.
Qed.

Lemma minpredP (P : nat -> bool) m :
  (forall n, (m <= n)%N -> P n) -> (lim (minpred P) <= m)%N.
Proof. move=>H. rewrite (minpred4 H) minpred6// H//. Qed.

Lemma minpred2 (P : nat -> bool) m :
  (forall n, (m <= n)%N -> P n) -> (forall n, (n >= (lim (minpred P)))%N -> P n).
Proof.
move=>H n. rewrite (minpred4 H)=>P1.
case E: (~~ (n < m))%N. move: E. rewrite -leqNgt. apply H.
move: E=>/negbFE/ltnW. by apply minpred5.
Qed.

Lemma minpred3 (P : nat -> bool) m :
  (forall n, (m <= n)%N -> P n) -> (forall n, ~~ P n -> (n < (lim (minpred P)))%N).
Proof.
move=>H n. apply contraNT. rewrite -leqNgt. apply (minpred2 H).
Qed.

Lemma rankingP (P: 'FO(U)) :
  (exists t, ranking_function P t) <-> 
  (forall x : 'FD(U), (fun n=>\Tr (P \o (whileso_incr M b D n) x)) --> 0)%classic.
have P0 : forall n (y : 'FD(U)), [den of whileso_incr M b D n.+1 y] = 
  [den of (D :o elemso M b) [den of whileso_incr M b D n y]].
by move=>n y; apply/val_inj; rewrite /= -whileso_incrED whileso_incrE soE.
split.
apply: contraPP. rewrite -existsNP -forallNP=>[[y Px] t].
move: Px. rewrite ccvg_subseqPN=>[[e [h [Ph [egt0 /= Pn]]]]].
rewrite /ranking_function -existsNP.
exists e. rewrite not_implyP.
split=>//. move=>/all_and2 [P11 P12].
pose t1 n := t e [den of (whileso_incr M b D n) y].
have Pt1 n : (t1 n.+1 <= t1 n)%N by rewrite /t1 P0 P11.
have Pt2 : forall m n, (n >= m -> t1 n <= t1 m)%N.
move=>m n /subnK => <-. elim: (n - m)%N => //= l ih.
rewrite addSn. apply: (leq_trans _ ih). apply Pt1. 
pose tt n := (t1 (h n)).
have Pc: forall n, (tt n.+1 < tt n)%N.
move=>n. rewrite /tt.
apply: (@leq_ltn_trans (t1 (h n).+1)).
by apply Pt2. rewrite /t1 P0. apply P12.
rewrite -[X in _ <= X]ger0_norm. apply trlfM_ge0; rewrite -psdlfE.
apply/obslf_psd/obsf_obs. apply/denlf_psd/denf_den.
by move: (Pn n); rewrite subr0.
apply (nat_well_founded Pc).
move=>H1.
pose Q c (x : 'FD(U)) := (fun n=> \Tr (P \o (whileso_incr M b D n) x) < c).
exists (fun c x => (lim (minpred (Q c x)))).
split.
all: move: (H1 x); rewrite ccvg_limP=>/(_ _ H)[N Pn];
have P1: (forall n, (N <= n)%N -> Q e x n)
by move=>n len; move: (Pn n len); rewrite /Q subr0 -[X in _ -> X < _]ger0_norm// 
?trlfM_ge0//=; [apply/obsf_ge0 | apply/denf_ge0].
all: have P3 n : Q e x n.+1 = (Q e ([den of (D :o elemso M b) x]) n)
by rewrite /Q whileso_incrED/= soE.
move: (minpred2 P1)=>P2. apply/minpredP=>n len. rewrite -P3.
apply P2. apply (leq_trans len). by [].
move: (minpred2 P1)=>P2 P4.
have P5: (lim (minpred (Q e x)) > 0)%N.
apply (minpred3 P1). rewrite /Q -real_leNgt/= ?soE//.
by apply gtr0_real. by apply ger0_real; apply: (le_trans _ P4); apply/ltW.
have P7 : forall n m, (n <= m = (n.+1 <= m.+1))%N. by [].
suff P6: lim (minpred (Q e x)) = (lim (minpred (Q e x))).-1.+1.
rewrite P6/= -P7.  
apply/minpredP=>n. rewrite -P3 -ltnS -P6. apply P2.
rewrite  -[_.-1.+1]addn1 -subn1 subnK//.
Qed.

End QOWhileRanking.
(* for quantum programs, we mostly work while. 
Instead of introducing the completeNormedModType of lfun, 
we provide a some lemmas to lim while *)

Section QOWhileLim.
Import CTopology.Exports HermitianTopology.Exports HermitianTopology.Theory VNorm.Exports.
Local Open Scope classical_set_scope.

Lemma trnorm_map m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q)) :
  linear f -> bijective f -> exists c, c > 0 /\ (forall x, \tr| f x | <= c * \tr| x |).
Proof.
move=>lf [g fK gK]. move: (@can2_linear _ _ _ (Linear lf))=>/=/(_ g fK gK) lg.
pose mn x := \tr| f x |.
have meq0 : forall x, mn x = 0 -> x = 0.
  by move=>x/normv0_eq0; rewrite -{2}(fK x)/==>->; rewrite (linearlfE lg) linear0.
have mtrg : forall x y, mn (x + y) <= mn x + mn y.
  by move=>x y; rewrite /mn (linearlfE lf) linearD lev_norm_add.
have mZ : forall (a: C) (x : 'M_(m,n)), mn (a *: x) = `|a| * mn x.
  by move=>a x; rewrite /mn (linearlfE lf) linearZ normvZ.
pose mvn := Vnorm mtrg meq0 mZ.
move: (cmxnormv_bounded mvn (@trnorm_vnorm _ _ _))=>[c /= cgt0 Pml].
exists c=>//.
Qed.

Lemma sobounded_apply (U V: chsType)  :
  exists c, (c > 0 /\ forall (f : 'SO(U,V)) x, `|f x| <= c * `|f| * `|x|).
Proof.
rewrite /normr/= /HermitianTopology.trfnorm /HermitianTopology.trsfnorm.
set f1 := (f2mx \o @r2v _ [vectType C of 'End(V)])%FUN.
have lf1 : linear f1 by move=>a b c; rewrite /f1 linearP.
have bf1 : bijective f1.
by exists (@v2r _ [vectType C of 'End(V)] \o Vector.Hom)%FUN;
move=>x/=; rewrite /f1/= ?v2rK// f2mxK r2vK.
move: (trnorm_map lf1 bf1)=>[c1 [c1gt0 Pc1]].
set f2 := (@v2r _ [vectType C of 'End(U)] \o Vector.Hom)%FUN.
have lf2 : linear f2 by move=>a b c; rewrite /f2 linearP.
have bf2 : bijective f2.
by exists (f2mx \o @r2v _ [vectType C of 'End(U)])%FUN;
move=>x/=; rewrite /f2/= ?v2rK// f2mxK r2vK.
move: (trnorm_map lf2 bf2)=>[c2 [c2gt0 Pc2]].
have c12gt0 : (c1 * c2 > 0) by apply mulr_gt0.
exists (c1 * c2); split=>// f x.
rewrite /normr/=/HermitianTopology.trfnorm /fun_of_superof unlock/=.
apply: (le_trans (Pc1 _)). rewrite -!mulrA ler_pmul2l// -trnorm_adjmx adjmxM.
apply: (le_trans (trnormM _ _)). rewrite trnorm_adjmx i2norm_adjmx [X in _ <= X]mulrC -mulrA.
apply ler_wpmul2l. apply/trnorm_ge0. apply: (le_trans (i2norm_trnorm _)).
move: (Pc2 (f2mx x)). by rewrite /f2/= f2mxK mulrC.
Qed.

Lemma so_cvg (U V: chsType) (f: nat -> 'SO(U,V)) (g : 'SO(U,V)) x :
  f --> g -> (fun i => f i x) --> g x.
Proof.
move/cvg_limP=>P; apply/cvg_limP=>e egt0.
move: (@sobounded_apply U V)=>[c [cgt0 Pc]]; case E: (`|x| == 0).
exists 0%N=>n _; first by move: E=>/eqP/normr0_eq0->; rewrite !linear0 addr0 normr0.
move: E=>/eqP/eqP E.
have xgt0 : (e / c / `|x| > 0) by
 apply divr_gt0; [apply divr_gt0 | rewrite normr_gt0 -normr_eq0].
move: (P _ xgt0)=>[N Pn]; exists N=>n len. 
rewrite -opp_soE -add_soE; apply: (le_lt_trans (Pc _ _)).
rewrite -mulrA mulrC -ltr_pdivl_mulr// -ltr_pdivl_mulr.
by rewrite normr_gt0 -normr_eq0. by apply Pn.
Qed.

Lemma so_is_cvg (U V: chsType) (f: nat -> 'SO(U,V)) x :
  cvg f -> cvg (fun i => f i x).
Proof. move/cvg_ex=>[a Pa]; apply/cvg_ex; exists (a x); by apply: so_cvg. Qed.

Lemma so_lim (U V: chsType) (f: nat -> 'SO(U,V)) x :
  cvg f -> lim (fun i => f i x) = (lim f) x.
Proof. by move=>cu; apply: cvg_lim; [apply: Vhausdorff | apply: so_cvg]. Qed.

Lemma hnorm_l2norm (U : chsType) (v : U) :
  `| v | = l2norm (v2r v).
Proof. 
rewrite /normr/= /hnorm dotp_mulmx mxE /l2norm pnorm_pair big_ord1.
by f_equal; apply eq_bigr=>i _; rewrite !mxE normCKC.
Qed.

Lemma fbnorm_trnorm (R : numClosedFieldType) m n (M : 'M[R]_(m,n)) :
  fbnorm M <= trnorm M.
Proof. by rewrite /fbnorm /trnorm /schattennorm l2norm_l1norm. Qed.

Lemma lfunbounded_apply (U V: chsType)  :
  exists c, (c > 0 /\ forall (f : 'Hom(U,V)) x, `|f x| <= c * `|f| * `|x|).
Proof.
rewrite {2}/normr/= /HermitianTopology.trfnorm.
exists 1. split=>//. apply: ltr01.
move=>f x. rewrite mul1r !hnorm_l2norm unlock/= r2vK.
apply: (le_trans (fbnorm_dotl _ _)).
apply ler_pmul. 1,2: apply: normv_ge0.
apply fbnorm_trnorm. apply i2norm_l2norm.
Qed.

Lemma lfun_cvg (U V: chsType) (f: nat -> 'Hom(U,V)) (g : 'Hom(U,V)) x :
  f --> g -> (fun i => f i x) --> g x.
Proof.
move/cvg_limP=>P; apply/cvg_limP=>e egt0.
move: (@lfunbounded_apply U V)=>[c [cgt0 Pc]]; case E: (`|x| == 0).
exists 0%N=>n _; first by move: E=>/eqP/normr0_eq0->; rewrite !linear0 addr0 normr0.
move: E=>/eqP/eqP E.
have xgt0 : (e / c / `|x| > 0) by
 apply divr_gt0; [apply divr_gt0 | rewrite normr_gt0 -normr_eq0].
move: (P _ xgt0)=>[N Pn]; exists N=>n len. 
rewrite -opp_lfunE -add_lfunE; apply: (le_lt_trans (Pc _ _)).
rewrite -mulrA mulrC -ltr_pdivl_mulr// -ltr_pdivl_mulr.
by rewrite normr_gt0 -normr_eq0. by apply Pn.
Qed.

Lemma lfun_is_cvg (U V: chsType) (f: nat -> 'Hom(U,V)) x :
  cvg f -> cvg (fun i => f i x).
Proof. move/cvg_ex=>[a Pa]; apply/cvg_ex; exists (a x); by apply: lfun_cvg. Qed.

Lemma lfun_lim (U V: chsType) (f: nat -> 'Hom(U,V)) x :
  cvg f -> lim (fun i => f i x) = (lim f) x.
Proof. by move=>cu; apply: cvg_lim; [apply: Vhausdorff | apply: lfun_cvg]. Qed.

Lemma while_sf_cvg (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U)) (f: 'End(U) -> C) x :
  scalar f -> ((fun n=>f ((whileso_iter M b D n) x)) --> f (whileso M b D x))%classic.
Proof. move=>sf; apply: linear_cvgP=>//; apply/so_cvg/whileso_cvg. Qed.

Lemma while_sf_is_cvg (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) (f: 'End(U) -> C) x :
  scalar f -> cvg (fun n=>f ((whileso_iter M b D n) x)).
Proof. move=>sf; apply: linear_is_cvgP=>//; apply/so_is_cvg/whileso_is_cvg. Qed.

Lemma while_sf_lim (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) (f: 'End(U) -> C) x :
  scalar f -> lim (fun n=>f ((whileso_iter M b D n) x)) = f (whileso M b D x).
Proof. move=>P. apply/cvg_lim. apply/Chausdorff. by apply/while_sf_cvg. Qed.

Lemma while_sf_ge_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvg c -> (\forall n \near \oo, c n <= f ((whileso_iter M b D n) x))
  -> lim c <= f (whileso M b D x).
Proof.
by move=>sf cc Pn; rewrite -while_sf_lim//; 
apply/ler_clim_near=>[//||//]; apply/while_sf_is_cvg.
Qed.

Lemma while_sf_ge (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvg c -> (forall n, c n <= f ((whileso_iter M b D n) x))
  -> lim c <= f (whileso M b D x).
Proof.
move=>sf cc Pn; rewrite -while_sf_lim//;
apply/ler_clim=>[//||//]; by apply/while_sf_is_cvg.
Qed.

Lemma while_sf_ge_cst_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (\forall n \near \oo, c <= f ((whileso_iter M b D n) x))
  -> c <= f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite ccvg_limE=>[[{17}<- P1]] P2 P3; by apply while_sf_ge_near.
Qed.

Lemma while_sf_ge_cst (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (forall n, c <= f ((whileso_iter M b D n) x))
  -> c <= f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite ccvg_limE=>[[{16}<- P1]] P2 P3; by apply while_sf_ge.
Qed.

Lemma while_sf_le_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvg c -> (\forall n \near \oo, f ((whileso_iter M b D n) x) <= c n)
  -> f (whileso M b D x) <= lim c.
Proof.
move=>sf cc Pn; rewrite -while_sf_lim//.
by apply/ler_clim_near=>[|//|//]; apply/while_sf_is_cvg.
Qed.

Lemma while_sf_le (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvg c -> (forall n, f ((whileso_iter M b D n) x) <= c n)
  -> f (whileso M b D x) <= lim c.
Proof.
move=>sf cc Pn; rewrite -while_sf_lim//;
apply/ler_clim=>[|//|//]; by apply/while_sf_is_cvg.
Qed.

Lemma while_sf_le_cst_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (\forall n \near \oo, f ((whileso_iter M b D n) x) <= c)
  -> f (whileso M b D x) <= c.
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite ccvg_limE=>[[{17}<- P1]] P2 P3; by apply while_sf_le_near.
Qed.

Lemma while_sf_le_cst (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (forall n, f ((whileso_iter M b D n) x) <= c)
  -> f (whileso M b D x) <= c.
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite ccvg_limE=>[[{16}<- P1]] P2 P3; by apply while_sf_le.
Qed.

Lemma clim_eq_near (f g : nat -> C) :
  cvg f -> (\forall n \near \oo, f n = g n) -> lim f = lim g.
Proof.
move=>/ccvg_limP cf [N _ Pn].
suff: g --> lim f by move/(cvg_lim (@Chausdorff _)).
apply/ccvg_limP=>e egt0.
move: (cf _ egt0)=>[M Pm].
exists (maxn N M)=>n Pnm.
rewrite -(Pn n)/=. apply: (leq_trans _ Pnm). apply/leq_maxl.
apply Pm. apply: (leq_trans _ Pnm). apply/leq_maxr.
Qed.

Lemma while_sf_eq_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f g : 'End(U) -> C) m x c :
  scalar f -> scalar g -> (\forall n \near \oo, 
    f ((whileso_iter M b D n) x) + c = g ((whileso_iter M b D (n+m)%N) x))
  -> f (whileso M b D x) + c = g (whileso M b D x).
Proof.
move=>sf sg P2. suff P1: cvg (fun n=>f (whileso_iter M b D n x) + c).
move: (clim_eq_near P1 P2). rewrite climD. by apply while_sf_is_cvg. apply: is_ccvg_cst.
rewrite clim_cst while_sf_lim// =>->.
move: (@while_sf_cvg _ M b D _ x sg). by rewrite -(cvg_shiftn m)=>/(cvg_lim (@Chausdorff _)).
apply is_ccvgD. by apply while_sf_is_cvg. apply: is_ccvg_cst.
Qed.

Lemma while_lf_cvg (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) x :
  ((fun n=>f ((whileso_iter M b D n) x)) --> f (whileso M b D x))%classic.
Proof.
apply: continuous_cvg. apply: linear_continuous.
apply so_cvg. apply whileso_cvg.
Qed.

Lemma while_lf_is_cvg (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) x :
  cvg (fun n=>f ((whileso_iter M b D n) x)).
Proof. by apply/cvg_ex; exists (f (whileso M b D x)); apply while_lf_cvg. Qed.

Lemma while_lf_lim (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) x :
  lim (fun n=>f ((whileso_iter M b D n) x)) = f (whileso M b D x).
Proof. apply/cvg_lim. apply/norm_hausdorff. by apply/while_lf_cvg. Qed.

Lemma while_lf_ge_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) (c: nat -> 'End(V)) x :
  cvg c -> (\forall n \near \oo, c n ⊑ f ((whileso_iter M b D n) x))
  -> lim c ⊑ f (whileso M b D x).
Proof.
by move=>cc Pn; rewrite -while_lf_lim//; 
apply/lev_lim_near=>[//||//]; apply/while_lf_is_cvg.
Qed.

Lemma while_lf_ge (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) (c: nat -> 'End(V)) x :
  cvg c -> (forall n, c n ⊑ f ((whileso_iter M b D n) x))
  -> lim c ⊑ f (whileso M b D x).
Proof.
move=>cc Pn; rewrite -while_lf_lim//;
apply/lev_lim=>[//||//]; by apply/while_lf_is_cvg.
Qed.

Lemma while_lf_ge_cst_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) c x :
  (\forall n \near \oo, c ⊑ f ((whileso_iter M b D n) x))
  -> c ⊑ f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite cvg_limE. apply: norm_hausdorff.
move=>[{17}<- P1] P3; by apply while_lf_ge_near.
Qed.

Lemma while_lf_ge_cst (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) c x :
  (forall n, c ⊑ f ((whileso_iter M b D n) x))
  -> c ⊑ f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite cvg_limE. apply norm_hausdorff.
move=>[{16}<- P1] P3; by apply while_lf_ge.
Qed.

Lemma while_lf_le_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) (c: nat -> 'End(V)) x :
  cvg c -> (\forall n \near \oo, f ((whileso_iter M b D n) x) ⊑ c n)
  -> f (whileso M b D x) ⊑ lim c.
Proof.
move=>cc Pn; rewrite -while_lf_lim//.
by apply/lev_lim_near=>[|//|//]; apply/while_lf_is_cvg.
Qed.

Lemma while_lf_le (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) (c: nat -> 'End(V)) x :
  cvg c -> (forall n, f ((whileso_iter M b D n) x) ⊑ c n)
  -> f (whileso M b D x) ⊑ lim c.
Proof.
move=>cc Pn; rewrite -while_lf_lim//;
apply/lev_lim=>[|//|//]; by apply/while_lf_is_cvg.
Qed.

Lemma while_lf_le_cst_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) c x :
  (\forall n \near \oo, f ((whileso_iter M b D n) x) ⊑ c)
  -> f (whileso M b D x) ⊑ c.
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite cvg_limE. apply norm_hausdorff.
move=>[{17}<- P1] P2; by apply while_lf_le_near.
Qed.

Lemma while_lf_le_cst (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) c x :
  (forall n, f ((whileso_iter M b D n) x) ⊑ c)
  -> f (whileso M b D x) ⊑ c.
Proof.
have: ((fun n:nat=>c) --> c)%classic by apply: cvg_cst.
rewrite cvg_limE. apply norm_hausdorff.
move=>[{16}<- P1] P2; by apply while_lf_le.
Qed.

Lemma lim_eqf_near (V: chsType) (f g : nat -> 'End(V)) :
  cvg f -> (\forall n \near \oo, f n = g n) -> lim f = lim g.
Proof.
move=>/cvg_limP cf [N _ Pn].
suff: g --> lim f by move/(cvg_lim (@norm_hausdorff _ _)).
apply/cvg_limP=>e egt0.
move: (cf _ egt0)=>[M Pm].
exists (maxn N M)=>n Pnm.
rewrite -(Pn n)/=. apply: (leq_trans _ Pnm). apply/leq_maxl.
apply Pm. apply: (leq_trans _ Pnm). apply/leq_maxr.
Qed.

Lemma while_lf_eq_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f g : 'Hom([vectType C of 'End(U)],[vectType C of 'End(V)])) m x c :
  (\forall n \near \oo, f ((whileso_iter M b D n) x) + c = g ((whileso_iter M b D (n+m)%N) x))
  -> f (whileso M b D x) + c = g (whileso M b D x).
Proof.
move=>P2. suff P1: cvg (fun n=>f (whileso_iter M b D n x) + c).
move: (lim_eqf_near P1 P2). rewrite limD. by apply while_lf_is_cvg. apply: is_cvg_cst.
rewrite lim_cst ?while_lf_lim// =>->.
move: (@while_lf_cvg _ _ M b D g x). by rewrite -(cvg_shiftn m)=>/(cvg_lim (@norm_hausdorff _ _)).
apply: is_cvgD. by apply while_lf_is_cvg. apply: is_cvg_cst.
Qed.

Lemma whileso_fixpoint (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) : 
  whileso M b D = ifso M (fun b'=> if b' == b then whileso M b D :o D
  else idso).
Proof.
apply/so_psdP=>x. rewrite psdlfE=>Px.
rewrite (ifso_boolE b) eqxx neqb !comp_soE soE.
apply/eqP. rewrite eq_le. apply/andP. split.
2: rewrite -lev_subr_addr.
all: rewrite -[X in X ⊑ _]id_lfunE; apply/while_lf_le_cst=>n; rewrite lfunE/=. 
case: n=>[|n]; first by rewrite /= soE addv_ge0=>[||//]; do 3 ? apply/cp_ge0.
2: move: (whileso_ub M b D n.+1)=>/leso_preserve_order/(_ Px); 
  rewrite lev_subr_addr; apply le_trans.
all: rewrite /= (ifso_boolE b) eqxx neqb !comp_soE soE lev_add2r. 2: by apply lexx.
apply/leso_preserve_order. apply/whileso_ub. by apply/cp_ge0/cp_ge0.
Qed.

Lemma whileso_incr_while (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) n :
  whileso M b D :o (whileso_incr M b D n) = whileso M b D - whileso_iter M b D n.
Proof.
elim: n=>[|n IH]; first by rewrite /= comp_so1r subr0.
rewrite whileso_incrE whileso_iterE opprD addrA -IH -linearBl/= !comp_soA.
f_equal. by rewrite {2}whileso_fixpoint (ifso_bool b) eqxx neqb comp_so1l addrK.
Qed.

Lemma whileso_incr_whileE (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) n x :
  whileso M b D (whileso_incr M b D n x) = whileso M b D x - whileso_iter M b D n x.
Proof. by move: (whileso_incr_while M b D n)=>/superopP/(_ x); rewrite !soE. Qed.

End QOWhileLim.

From mathcomp Require Import finset.

Section ComplementObs.
Variable (U : chsType).

Definition cplmt (P : 'End(U)) := \1 - P.
Lemma cplmtE (P : 'End(U)) : \1 - P = cplmt P. Proof. by []. Qed.

Lemma cplmtK P : cplmt (cplmt P) = P.
Proof. by rewrite /cplmt opprB addrC addrNK. Qed.

Lemma cplmt1 : cplmt \1 = 0.
Proof. by rewrite /cplmt subrr. Qed.

Lemma cplmt0 : cplmt 0 = \1.
Proof. by rewrite -cplmt1 cplmtK. Qed.

(* canonical structures *)
Lemma cplmt_obs (P : 'FO(U)) : cplmt P \is obslf.
Proof. 
by move: (obsf_obs P); rewrite !lef_obs subv_ge0 lev_subl_addr lev_addl=>/andP[->->].
Qed.
Canonical cplmt_obsfType P := ObsfType (@cplmt_obs P).
Lemma cplmt_proj (P : 'FP(U)) : cplmt P \is projlf.
Proof.
apply/projlfP; split. apply/hermlfP/obslf_herm/obsf_obs.
rewrite /cplmt linearBl/= !linearBr/= !comp_lfun1l comp_lfun1r.
by move: (projf_proj P)=>/projlfP[_ ->]; rewrite addrN subr0.  
Qed.
Canonical cplmt_projfType P := ProjfType (@cplmt_proj P).

Lemma cplmt_dualC (E: 'QC(U)) (P:'FO(U)) : 
  cplmt (E^*o P) = E^*o (cplmt P).
Proof. by rewrite /cplmt linearB/= dual_qc1_eq1. Qed.
Lemma cplmt_lef (P Q : 'End(U)) : P ⊑ Q = (cplmt Q ⊑ cplmt P).
Proof. by rewrite lev_subl_addl addrA lev_subr_addl lev_add2r. Qed. 

End ComplementObs.

Arguments cplmt {U} P.
Notation "P '^⟂'" := (cplmt P).

Section SOTensor.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T: {set L}).
Local Notation idx := (@idx _ H).

Definition tenso_fun S T S' T' (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) 
  (x : 'F[H]_(S :|: S')) : 'F[H]_(T :|: T')
  := \sum_(i : idx (S :|: S')) \sum_(j : idx (S :|: S')) (
    [< deltav i ; x (deltav j) >] *: 
    ( E [> (deltav (idxSl i)) ; (deltav (idxSl j)) <] \⊗ 
      F [> (deltav (idxSr i)) ; (deltav (idxSr j)) <] )).

Lemma tenso_fun_is_linear S T S' T' (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  linear (tenso_fun E F).
Proof.
move=>a u v; rewrite /tenso_fun.
do 2 (rewrite scaler_sumr -big_split /=; apply eq_bigr=>? _).
by rewrite lfunE/= lfunE/= linearP/= scalerA -scalerDl.
Qed.
Canonical tenso_fun_linear S T S' T' E F := Linear (@tenso_fun_is_linear S T S' T' E F).
Definition tenso S T S' T' E F := Superop (linfun (@tenso_fun S T S' T' E F)).

Notation "f :⊗ g" := (tenso f g).

Lemma tensodf S T S' T' (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) (i j : idx (S :|: S')) :
  E [> (deltav (idxSl i)) ; (deltav (idxSl j)) <] \⊗ 
  F [> (deltav (idxSr i)) ; (deltav (idxSr j)) <]
  = tenso E F [> deltav i ; deltav j <]. 
Proof.
rewrite /tenso {3}/fun_of_superof/= lfunE/= /tenso_fun.
rewrite (bigD1 i)//= (bigD1 j)//= !big1=>[k/negPf nk|k/negPf nk|].
2: rewrite big1// =>[l _].
all: rewrite outpE linearZ/= !onb_dot ?nk 1?eq_sym ?nk ?mul0r ?mulr0 ?scale0r//.
by rewrite !eqxx mulr1 scale1r !addr0.
Qed.

Lemma tenso_correct S T S' T' (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) : 
  [disjoint S & S'] ->
  forall (u : 'F_S) (v : 'F_S'), (E u) \⊗ (F v) = (tenso E F) (u \⊗ v).
Proof.
move=>dis u v.
rewrite (onb_lfun2id deltav_onbasis u).
rewrite linear_suml !linear_sum linear_suml/=. apply eq_bigr=>i _.
rewrite linear_suml !linear_sum linear_suml/=. apply eq_bigr=>j _.
rewrite (onb_lfun2id deltav_onbasis v).
rewrite linear_sumr !linear_sum/=. apply eq_bigr=>m _.
rewrite linear_sumr !linear_sum/=. apply eq_bigr=>n _.
rewrite 5 !linearZ/=; f_equal; rewrite 2 !linearZl linearZ/=; f_equal.
by rewrite tenf_outp !deltavtV//= -tensodf !idxSUl//= !idxSUr//=.
Qed.

Lemma superopPD S T (A B : 'SO[H]_(S,T)) : 
  (forall (i j : idx S), A [> deltav i ; deltav j <] = B [> deltav i ; deltav j <]) <-> A = B.
Proof.
split=>[P|->//]; apply/superopP=>x; rewrite (onb_lfun2id deltav_onbasis x).
do 2 (rewrite !linear_sum/=; apply eq_bigr=>? _).
by rewrite !linearZ/= P.
Qed.

Lemma linear_tenso S T S' T' E : linear (@tenso S T S' T' E).
Proof.
move=>a v w. apply/superopPD=>i j.
by rewrite !soE -!tensodf !soE linearPr.
Qed.
Canonical tenso_additive S T S' T' E := Additive (@linear_tenso S T S' T' E).
Canonical tenso_linear S T S' T' E := Linear (@linear_tenso S T S' T' E).
Definition tensor S T S' T' E := (@tenso S T S' T')^~ E.
Lemma linear_tensor S T S' T' E : linear (@tensor S T S' T' E).
Proof.
move=>a v w. apply/superopPD=>i j.
by rewrite !soE -!tensodf !soE linearPl.
Qed.
Canonical tensor_additive S T S' T' E := Additive (@linear_tensor S T S' T' E).
Canonical tensor_linear S T S' T' E := Linear (@linear_tensor S T S' T' E).
Canonical tenso_rev S T S' T' := 
  [revop (@tensor S T S' T') of (@tenso S T S' T')].
Canonical tenso_is_bilinear S T S' T' := [bilinear of (@tenso S T S' T')].

Lemma tenso_comp S T S' T' W W' (f1: 'SO[H]_(S,T)) (f2: 'SO[H]_(W,S)) 
  (g1: 'SO[H]_(S',T')) (g2: 'SO[H]_(W',S')) : [disjoint S & S'] ->
  (f1 :o f2) :⊗ (g1 :o g2) = (f1 :⊗ g1) :o (f2 :⊗ g2).
Proof.
move=>dis; apply/superopPD=>i j.
by rewrite comp_soE -!tensodf !comp_soE -tenso_correct.
Qed.

Lemma tenso_compr S T S' T' W W' (f1: 'SO[H]_(S,T)) (f2: 'SO[H]_(T,W)) 
  (g1: 'SO[H]_(S',T')) (g2: 'SO[H]_(T',W')) : [disjoint T & T'] ->
  (f1 o: f2) :⊗ (g1 o: g2) = (f1 :⊗ g1) o: (f2 :⊗ g2).
Proof. by move=>dis; rewrite !comp_soErl tenso_comp. Qed.

Lemma tenso_dual S T S' T' (f: 'SO[H]_(S,T)) (g: 'SO[H]_(S',T')) :
  (f :⊗ g)^*o = f^*o :⊗ g^*o.
Proof.
apply/superopPD=>i j. apply/trlf_introdvl=>m n.
rewrite -dualso_trlfE -!tensodf lftraceC !trlf_deltavl -!dualso_trlfE.
by f_equal; rewrite lftraceC.
Qed.

End SOTensor.

Notation "f :⊗ g" := (tenso f g).

Section SOTensorBilinear.
Context {L : finType} (H : L -> chsType).
Variables (S T S' T' : {set L}).
Implicit Type (f: 'SO[H]_(S,T)) (g: 'SO[H]_(S',T')).

Lemma tenso0 f : f :⊗ (0: 'SO[H]_(S',T')) = 0.
Proof. exact: linear0r. Qed.

Lemma ten0so g : (0: 'SO[H]_(S,T)) :⊗ g = 0.
Proof. exact: linear0l. Qed.

Lemma tenso11 : (:1 : 'SO[H]_S) :⊗ (:1: 'SO[H]_S') = :1.
Proof. by apply/superopPD=>i j; rewrite -tensodf !soE tenf_outp !deltavt. Qed.

Lemma tensoDl g (f1 f2: 'SO[H]_(S,T)) : (f1 + f2) :⊗ g = (f1 :⊗ g) + (f2 :⊗ g).
Proof. exact: linearDl. Qed.

Lemma tensoDr f (g1 g2: 'SO[H]_(S',T')) : f :⊗ (g1 + g2) = (f :⊗ g1) + (f :⊗ g2).
Proof. exact: linearDr. Qed.

Lemma tensoNl g f : (- f) :⊗ g = - (f :⊗ g).
Proof. exact: linearNl. Qed.

Lemma tensoNr f g : f :⊗ (- g) = - (f :⊗ g).
Proof. exact: linearNr. Qed.

Lemma tensoZl g (c: C) f : (c *: f) :⊗ g = c *: (f :⊗ g).
Proof. exact: linearZl. Qed.

Lemma tensoZr f (c: C) g : f :⊗ (c *: g) = c *: (f :⊗ g).
Proof. exact: linearZr. Qed.

Lemma tensoBl g f1 f2 : (f1 - f2) :⊗ g = f1 :⊗ g - f2 :⊗ g.
Proof. exact: linearBl. Qed.

Lemma tensoBr f g1 g2 : f :⊗ (g1 - g2) = f :⊗ g1 - f :⊗ g2.
Proof. exact: linearBr. Qed.

Lemma tensoPl g (c: C) f1 f2: (c *: f1 + f2) :⊗ g = c *: (f1 :⊗ g) + (f2 :⊗ g).
Proof. exact: linearPl. Qed.

Lemma tensoPr f (c: C) g1 g2 : f :⊗ (c *: g1 + g2) = c *: (f :⊗ g1) + (f :⊗ g2).
Proof. exact: linearPr. Qed.

Lemma tensoMnl g f n : (f *+ n) :⊗ g = (f :⊗ g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma tensoMnr f g n : f :⊗ (g *+ n) = (f :⊗ g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma tensoMNnl g f n : (f *- n) :⊗ g = (f :⊗ g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma tensoMNnr f g n : f :⊗ (g *- n) = (f :⊗ g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma tenso_suml g I r (P: pred I) (E: I -> 'SO[H]_(S, T)) :
 (\sum_(i <- r | P i) E i) :⊗ g = \sum_(i <- r | P i) (E i :⊗ g).
Proof. exact: linear_suml. Qed.

Lemma tenso_sumr f I r (P: pred I) (E: I -> 'SO[H]_(S', T')) :
 f :⊗ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (f :⊗ E i).
Proof. exact: linear_sumr. Qed.

Lemma tenso_comp1r W f (h: 'SO[H]_(W,S)) : [disjoint S & S'] -> 
  (f :o h) :⊗ (:1 : 'SO[H]_S') = (f :⊗ :1) :o (h :⊗ :1).
Proof. by move=>dis; rewrite -tenso_comp ?comp_so1l//. Qed.

Lemma tenso_comp1l W f (h: 'SO[H]_(W,S)) : [disjoint S' & S] -> 
  (:1 : 'SO[H]_S') :⊗ (f :o h) = (:1 :⊗ f) :o (:1 :⊗ h).
Proof. by move=>dis; rewrite -tenso_comp ?comp_so1l//. Qed.

Lemma tenso_compr1r W f (h: 'SO[H]_(T,W)) : [disjoint T & T'] -> 
  (f o: h) :⊗ (:1 : 'SO[H]_T') = (f :⊗ :1) o: (h :⊗ :1).
Proof. by move=>dis; rewrite -tenso_compr ?comp_sor1l//. Qed.

Lemma tenso_compr1l W f (h: 'SO[H]_(T,W)) : [disjoint T' & T] -> 
  (:1 : 'SO[H]_T') :⊗ (f o: h) = (:1 :⊗ f) o: (:1 :⊗ h).
Proof. by move=>dis; rewrite -tenso_compr ?comp_sor1l//. Qed.

End SOTensorBilinear.

Section CastSO.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T : {set L}).

Definition castso S T S' T' (eqST : (S = S') * (T = T')) (f : 'SO[H]_(S,T)) : 
  'SO[H]_(S',T') :=
  let: erefl in _ = T' := eqST.2 return 'SO[H]_(S',T') in
    let: erefl in _ = S' := eqST.1 return 'SO[H]_(S',T) in f.

Lemma castso_id S T erefl_ST (f : 'SO[H]_(S,T)) : castso erefl_ST f = f.
Proof. by case: erefl_ST => e_S e_T; rewrite [e_S]eq_axiomK [e_T]eq_axiomK. Qed.

Lemma castsoE S T S' T' (eqST : (S = S') * (T = T')) (f : 'SO[H]_(S,T)) u :
  castso eqST f u = castlf (eqST.2,eqST.2) (f (castlf (esym eqST.1,esym eqST.1) u)).
Proof. 
by do [case: eqST; case: S' /; case: T' /] in f u *; rewrite !castlf_id castso_id.
Qed.

Lemma castso_comp S1 T1 S2 T2 S3 T3 (eq_S1 : S1 = S2) (eq_T1 : T1 = T2)
                                    (eq_S2 : S2 = S3) (eq_T2 : T2 = T3) f :
  castso (eq_S2, eq_T2) (castso (eq_S1, eq_T1) f)
    = castso (etrans eq_S1 eq_S2, etrans eq_T1 eq_T2) f.
Proof.
by case: S2 / eq_S1 eq_S2; case: S3 /; case: T2 / eq_T1 eq_T2; case: T3 /.
Qed.

Lemma castsoK S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) :
 cancel (castso (eq_S, eq_T)) (castso (esym eq_S, esym eq_T)).
Proof. by case: S2 / eq_S; case: T2 / eq_T. Qed.

Lemma castsoKV S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) :
 cancel (castso (esym eq_S, esym eq_T)) (castso (eq_S, eq_T)).
Proof. by case: S2 / eq_S; case: T2 / eq_T. Qed.

(* This can be use to reverse an equation that involves a cast. *)
Lemma castso_sym S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) A1 A2 :
 A1 = castso (eq_S, eq_T) A2 -> A2 = castso (esym eq_S, esym eq_T) A1.
Proof. by move/(canLR (castsoK _ _)). Qed.

Lemma castso_symV S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) A1 A2 :
  A2 = castso (esym eq_S, esym eq_T) A1 -> A1 = castso (eq_S, eq_T) A2.
Proof. by move/(canLR (castsoKV _ _)). Qed.

Lemma castso_is_linear S T S' T' (eqST : (S = S') * (T = T')) : 
  linear (@castso _ _ _ _ eqST).
Proof. 
move=>a f g; case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT.
by rewrite !castso_id.
Qed.
Canonical castso_linear S T S' T' (eqST : (S = S') * (T = T')) :=
  Linear (castso_is_linear eqST).

Lemma castso_compl S T S' T' (eqST: S = T') (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  castso (eqST, erefl _) f :o g = f :o castso (erefl _, esym eqST) g.
Proof.
by move: f g; case: T' / eqST => f g; rewrite !castso_id.
Qed.

Lemma castso_complV S T S' T' (eqST: T' = S) (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  f :o castso (erefl _, eqST) g = castso (esym eqST, erefl _) f :o g.
Proof.
by move: f g; case: S / eqST => f g; rewrite !castso_id.
Qed.

Lemma castso_compr S T S' T' (eqST: T = S') (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  castso (erefl _, eqST) f o: g = f o: castso (esym eqST, erefl _) g.
Proof.
by move: f g; case: S' / eqST => f g; rewrite !castso_id.
Qed.

Lemma castso_comprV S T S' T' (eqST: S' = T) (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  f o: castso (eqST, erefl _) g = castso (erefl _, esym eqST) f o: g.
Proof.
by move: f g; case: T / eqST => f g; rewrite !castso_id.
Qed.

Lemma compso_cast S W T S' W' T' (A : 'SO[H]_(W,T)) (B : 'SO[H]_(S,W)) 
  (eqW : W = W') (eqT: T = T') (eqS: S = S') :
    castso (eqW,eqT) A :o castso (eqS,eqW) B = castso (eqS,eqT) (A :o B).
Proof. by case: W' / eqW; case: T' /eqT; case: S' /eqS; rewrite !castso_id. Qed.

Lemma compso_castl S W T T' (A : 'SO[H]_(W,T)) (B : 'SO[H]_(S,W)) (eqT: T = T') :
    castso (erefl _, eqT) A :o B = castso (erefl,eqT) (A :o B).
Proof. by case: T' /eqT; rewrite !castso_id. Qed.

Lemma compso_castr S W T S' (A : 'SO[H]_(W,T)) (B : 'SO[H]_(S,W)) (eqS: S = S') :
    A :o castso (eqS,erefl) B = castso (eqS,erefl) (A :o B).
Proof. by case: S' /eqS; rewrite !castso_id. Qed.

Lemma castso_dual S T S' T' (eqST : (S = S') * (T = T')) (f: 'SO[H]_(S,T)) : 
  (castso eqST f)^*o = castso (eqST.2,eqST.1) f^*o.
Proof.
by do [case: eqST; case: S' /; case: T' /] in f *; rewrite !castso_id.
Qed.

Lemma castso1 S T (eqST : (S = T)) :  (castso (eqST,eqST) :1) = :1.
Proof. by case: T / eqST; rewrite castso_id. Qed.

Lemma castso0 S T S' T' (eqST : (S = S') * (T = T')) :  (castso eqST 0) = 0.
Proof. by rewrite linear0. Qed.

Lemma leso_cast S T S' T' (eqST : (S = S') * (T = T')) (E F : 'SO[H]_(S,T)) :
  castso eqST E ⊑ castso eqST F = (E ⊑ F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1; case: T' / eq2; rewrite !castso_id. Qed.

Lemma ltso_cast S T S' T' (eqST : (S = S') * (T = T')) (E F : 'SO[H]_(S,T)) :
  castso eqST E ⊏ castso eqST F = (E ⊏ F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1; case: T' / eq2; rewrite !castso_id. Qed.

Lemma leso_cast_sym S S' T T' (eqST : (S = S') * (T = T')) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  castso eqST E ⊑ F = (E ⊑ castso (esym eqST.1, esym eqST.2) F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1 F; case: T' / eq2=>F; rewrite !castso_id. Qed.

Lemma leso_cast_symV S S' T T' (eqST : (S' = S) * (T' = T)) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  E ⊑ castso eqST F = (castso (esym eqST.1, esym eqST.2) E ⊑ F).
Proof. by case: eqST => eq1 eq2; case: S / eq1 E; case: T / eq2=>E; rewrite !castso_id. Qed.

Lemma ltso_cast_sym S S' T T' (eqST : (S = S') * (T = T')) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  castso eqST E ⊏ F = (E ⊏ castso (esym eqST.1, esym eqST.2) F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1 F; case: T' / eq2=>F; rewrite !castso_id. Qed.

Lemma ltso_cast_symV S S' T T' (eqST : (S' = S) * (T' = T)) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  E ⊏ castso eqST F = (castso (esym eqST.1, esym eqST.2) E ⊏ F).
Proof. by case: eqST => eq1 eq2; case: S / eq1 E; case: T / eq2=>E; rewrite !castso_id. Qed.

End CastSO.

Require Import setdec.

(* partial trace is a quantum channel *)
Section PartialTrace.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W : {set L}).

Lemma setDI S T : (S :\: T) :|: (S :&: T) = S.
Proof. by rewrite setUC setID. Qed.

Definition ptraceso_fun T S (x : 'F[H]_S) : 'F[H]_(S :\: T) :=
    \sum_(k : 'Idx[H]_(S :&: T))
    \sum_(i : 'Idx[H]_(S :\: T)) \sum_(j : 'Idx[H]_(S :\: T))
    ([< deltav (idxU k i); castlf (esym (setID S T), esym (setID S T)) x (deltav (idxU k j)) >] 
     *: [>deltav i ; deltav j <]).
Lemma ptraceso_fun_is_linear S T : linear (@ptraceso_fun S T).
Proof.
move=>a x y. rewrite /ptraceso_fun.
do 3 (rewrite scaler_sumr -big_split /=; apply eq_bigr=>? _).
by rewrite linearP/= lfunE/= lfunE/= linearP/= scalerDl scalerA.
Qed.
Canonical ptraceso_fun_linear T S := Linear (@ptraceso_fun_is_linear T S).
Definition ptraceso T S := Superop (linfun (@ptraceso_fun T S)).

Notation "'\Tr_' ( T ) f " := (@ptraceso T _ f).

Lemma ptraceso_krausso T S : @ptraceso T S =
  krausso (fun i : 'Idx[H]_(S :&: T) => castlf ((setID _ _), set0U _) 
    ([> deltav (idx0 H); deltav i <] \⊗ (\1 : 'F_(S :\: T)))).
Proof.
move: (disjointID S T)=>dis.
apply/superopPD=>i j.
rewrite soE /ptraceso {1}/fun_of_superof/= lfunE/= /ptraceso_fun.
apply eq_bigr=>k _.
rewrite (bigD1 (idxSr (castidx (esym (setID S T)) i)))//= 
  (bigD1 (idxSr (castidx (esym (setID S T)) j)))//= !big1=>[i0/negPf ni|i0/negPf ni|].
2: rewrite big1// =>j0 _.
all: rewrite castlf_outp/= !deltav_cast outpE linearZ/= !deltavt
  !idxSUl// !idxSUr// !tenv_dot// !onb_dot.
1,2: by rewrite ?ni ?[_==i0]eq_sym ?ni ?(mulr0,mul0r) scale0r.
rewrite !eqxx !mulr1 !addr0 castlf_adj/= tenf_adj adjf1 adj_outp.
rewrite castlf_complfG/= -[castlf (esym (setID S T),_) _](mul_cast _ _ (esym (setID S T)))/=.
rewrite castlf_comp !etransE !mul_castl castlf_comp !etransE.
rewrite castlf_outp/= !deltav_cast !deltavt -tenf_outp -!tenf_comp//.
rewrite comp_lfun1l comp_lfun1r outp_comp linearZl/= outp_comp -!cdvE !cdvdelta.
rewrite scalerA mulrC linearZl/= linearZ outp_idx0/=. f_equal.
by apply/cf_eq; rewrite cf_castK -tenf1l.
Qed.

Lemma ptraceso_cp T S : @ptraceso T S \is iscp.
Proof. by rewrite ptraceso_krausso cp_iscpP. Qed.
Canonical ptraceso_cpType T S := CPType (@ptraceso_cp T S).
Lemma ptraceso_qc T S : @ptraceso T S \is isqc.
Proof.
move: (disjointID S T)=>dis; apply/cp_isqcP=>x.
rewrite (castlf_trlf (esym (setID S T)) x) [X in _ = \Tr X](onb_lfun2id deltav_onbasis).
rewrite /= /ptraceso /fun_of_superof/= lfunE/= /ptraceso_fun.
rewrite !linear_sum/= idxSsum//.
apply eq_bigr=>i _. rewrite exchange_big/= linear_sum/=.
apply eq_bigr=>j _. rewrite idxSsum// exchange_big !linear_sum/=.
apply eq_bigr=>k _. rewrite linear_sum/= (bigD1 i)//= big1=>[m/negPf nm|].
all: rewrite !linearZ/= !outp_trlf ?addr0; do ? f_equal.
suff ->: [< deltav (idxU i j); deltav (idxU m k) >] = 0 by rewrite mulr0.
all: by rewrite !deltavt tenv_dot// !idxSUl// !idxSUr// !onb_dot ?eqxx ?mul1r//
  [i == m]eq_sym nm mul0r.
Qed.
Canonical ptraceso_qcType T S := QCType (@ptraceso_qc T S).
Lemma ptraceso_qo T S : @ptraceso T S \is isqo.
Proof. apply/isqc_qo/ptraceso_qc. Qed.
Canonical ptraceso_qoType T S := QOType (@ptraceso_qo T S).

Lemma castso_krausso S T S' T' (eqST : (S = S') * (T = T')) (F : finType) 
  (f : F -> 'F[H]_(S,T)) :
  castso eqST (krausso f) = krausso (fun i=> castlf eqST (f i)).
Proof. by case: eqST=>eqS eqT; case: S' / eqS; case: T' /eqT. Qed.

Lemma ptraceso_comp T W S : 
@ptraceso T _ :o @ptraceso W S = 
castso (erefl _, esym (setDDl _ _ _)) (@ptraceso (W :|: T) S).
Proof.
rewrite !ptraceso_krausso comp_krausso castso_krausso.
suff P1 : ((S :\: W) :&: T) :|: (S :&: W) = S :&: (W :|: T).
suff P2 : [disjoint (S :\: W) :&: T & S :&: W].
pose h (i : 'Idx[H]__) := (idxSl (castidx (esym P1) i), idxSr (castidx (esym P1) i)).
pose g i := castidx P1 (idxU i.1 i.2 : 'Idx[H]__).
have hK : cancel h g by move=>x; rewrite /h /g/= idxUS// castidx_comp castidx_id.
have gK : cancel g h by move=>x; rewrite /h /g/= castidx_comp castidx_id 
  idxSUl// idxSUr// -surjective_pairing.
have bh : bijective h by exists g.
apply: (krausso_reindex bh)=>i/=.
apply/cf_eq. rewrite -dotf_mul !castlf_out !cf_castK.
have ->: [> deltav (idx0 H); deltav i <] =
castlf (P1, setU0 _) ( castlf (setUC _ _, setUC _ _) (
[> deltav (idx0 H); deltav (idxSr (castidx (esym P1) i)) <] \⊗
[> deltav (idx0 H); deltav (idxSl (castidx (esym P1) i)) <])).
by rewrite tenf_castC tenf_outp -deltavt deltavtV ?disjoint0X// castlf_outp/= 
  !deltav_cast idx0E castidx_comp castidx_id.
rewrite !castlf_out !cf_castK -tenfA tenfC -dotf_ten_cond.
rewrite /dot_lfun. apply: cf_comp; rewrite ?cf_castK -tenfA tenf11 -?tenfA ?tenf11.
1,2: do ? apply: cf_tens=>//. 1,2: apply/cf_implicit1.
all: fsetdec L.
Qed.

End PartialTrace.

(* move *)
Section Outp.
Implicit Type (H G : chsType).

Lemma outp_eq0 H G (u : H) (v : G) :
  [> u ; v <] == 0 = ((u == 0) || (v == 0)).
Proof.
case E: (u == 0); first by move: E=>/eqP->; rewrite linear0l eqxx.
case Ev: (v == 0); first by move: Ev=>/eqP->; rewrite linear0r eqxx.
case: eqP=>// /lfunP/(_ v)/eqP.
by rewrite outpE lfunE/= scaler_eq0 E dotp_eq0 Ev.
Qed.

Lemma outp_ge0 G (v : G) : (0 : 'End(G)) ⊑ [> v ; v <].
Proof. 
apply/lef_dot=>u; rewrite lfunE/= linear0 outpE 
  linearZ/= -conj_dotp -normCKC exprn_ge0//.
Qed.
Lemma outp_psd G (v : G) : [> v ; v <] \is psdlf.
Proof. by rewrite psdlfE outp_ge0. Qed.
Canonical outp_psdfType G v := PsdfType (@outp_psd G v).
Canonical outp_hermfType G (v : G) := Eval hnf in 
  [herm of [> v ; v <] as [herm of [psd of [> v ; v <]]]].
Lemma outp_proj1 G (v : 'NS(G)) : [> v; v <] \is proj1lf.
Proof.
apply/proj1lfP; split; last by rewrite outp_trlf ns_dot.
by apply/projlfP; rewrite adj_outp outp_comp ns_dot scale1r.
Qed.
Canonical outp_proj1fType G v := Proj1fType (@outp_proj1 G v).
Canonical outp_projfType (G : chsType) (v : 'NS(G)) := Eval hnf in 
  [proj of [> v ; v <] as [proj of [proj1 of [> v ; v <]]]].
Canonical outp_obsfType (G : chsType) (v : 'NS(G)) := Eval hnf in 
  [obs of [> v ; v <] as [obs of [proj1 of [> v ; v <]]]].
Canonical outp_den1fType (G : chsType) (v : 'NS(G)) := Eval hnf in 
  [den1 of [> v ; v <] as [den1 of [proj1 of [> v ; v <]]]].
Canonical outp_denfType (G : chsType) (v : 'NS(G)) := Eval hnf in 
  [den of [> v ; v <] as [den of [proj1 of [> v ; v <]]]].

Lemma outp_le1 G (v : G) : [< v ; v >] <= 1 -> [> v; v <] ⊑ \1.
Proof.
move=>P. apply/lef_dot=>u; rewrite outpE dotpZr -conj_dotp -normCKC.
by apply: (le_trans (CauchySchwartz _ _)); rewrite lfunE/= ler_pimulr// ge0_dotp.
Qed.
Lemma ns_outp_le1 G (v : 'NS(G)) : [> v; v <] ⊑ \1.
Proof. by apply outp_le1; rewrite ns_dot. Qed.

End Outp.


Definition chs0 (U: chsType) : 'I_(Vector.dim U) := cast_ord (chsdim _) ord0.
Arguments chs0 {U}.

Section SOTensorTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W : {set L}).

Lemma tenso_krausso S T S' T' (dis : [disjoint S & S']) (F G : finType) 
  (f : F -> 'F[H]_(S,T)) (g : G -> 'F[H]_(S',T')) :
  krausso f :⊗ krausso g = krausso (fun i : F * G => f i.1 \⊗ g i.2).
Proof.
apply/superopPD=>i j; rewrite -tensodf !soE linear_suml/=.
under eq_bigr do rewrite linear_sum/=.
rewrite pair_big/=; apply eq_bigr=>[[m n]] _/=.
by rewrite !tenf_comp// tenf_outp tenf_adj !deltavt.
Qed.

Lemma tenso_krausso_formso S T S' T' (dis : [disjoint S & S']) (F : finType) 
  (f : F -> 'F[H]_(S,T)) (g : 'F[H]_(S',T')) :
  krausso f :⊗ formso g = krausso (fun i : F => f i \⊗ g).
Proof.
rewrite tenso_krausso//.
have bh: bijective (fun i : F => (i,ord0 : 'I_1)).
by exists (fun i=>i.1)=>x//=; case: x=>a b; rewrite ord1/=.
by apply: (krausso_reindex bh).
Qed.

Lemma tenso_formso_krausso S T S' T' (dis : [disjoint S & S']) (F : finType) 
  (g : 'F[H]_(S,T)) (f : F -> 'F[H]_(S',T')) :
  formso g :⊗ krausso f = krausso (fun i : F => g \⊗ f i).
Proof.
rewrite tenso_krausso//.
have bh: bijective (fun i : F => (ord0 : 'I_1, i)).
by exists (fun i=>i.2)=>x//=; case: x=>a b; rewrite !ord1/=.
by apply: (krausso_reindex bh).
Qed.

Lemma tenso_formso S T S' T' (dis : [disjoint S & S']) (f : 'F[H]_(S,T)) (g : 'F[H]_(S',T')) :
  formso f :⊗ formso g = formso (f \⊗ g).
Proof.
apply/superopPD=>i j.
by rewrite -tensodf !soE !tenf_comp// tenf_outp tenf_adj !deltavt.
Qed.

Definition lift_lf S T (sub : S :<=: T) (f : 'F[H]_S) : 'F[H]_T :=
  castlf (setUD_sub sub, setUD_sub sub) (f \⊗ (\1 : 'F[H]_(T :\: S))). 

Definition liftso S T (sub : S :<=: T) (E : 'SO[H]_S) : 'SO[H]_T :=
  castso (setUD_sub sub, setUD_sub sub) (E :⊗ (:1 : 'SO[H]_(T :\: S))).

Definition lift_fun S T (sub : S :<=: T) (F : finType) (f : F -> 'F[H]_S) :=
  (fun i : F => lift_lf sub (f i)).

Lemma castso_cpE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  castso eqST E \is iscp = (E \is iscp).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_cp S T S' T' (eqST : (S = S') * (T = T')) (E: 'CP[H]_(S,T)) :
  castso eqST E \is iscp.
Proof. by rewrite castso_cpE cp_iscpP. Qed.
Canonical castso_cpType S T S' T' eqST E := CPType (@castso_cp S T S' T' eqST E).

Lemma castso_qoE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  castso eqST E \is isqo = (E \is isqo).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_qo S T S' T' (eqST : (S = S') * (T = T')) (E: 'QO[H]_(S,T)) :
  castso eqST E \is isqo.
Proof. by rewrite castso_qoE qo_isqoP. Qed.
Canonical castso_qoType S T S' T' eqST E := QOType (@castso_qo S T S' T' eqST E).

Lemma castso_qcE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  castso eqST E \is isqc = (E \is isqc).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_qc S T S' T' (eqST : (S = S') * (T = T')) (E: 'QC[H]_(S,T)) :
  castso eqST E \is isqc.
Proof. by rewrite castso_qcE qc_isqcP. Qed.
Canonical castso_qcType S T S' T' eqST E := QCType (@castso_qc S T S' T' eqST E).

Lemma tenso_cp S T S' T' (dis : [disjoint S & S']) (E : 'CP[H]_(S,T)) (F : 'CP[H]_(S',T')) :
  tenso E F \is iscp.
Proof. by rewrite krausopE (krausopE F) tenso_krausso// cp_iscpP. Qed.
Canonical tenso_cpType S T S' T' dis E F := CPType (@tenso_cp S T S' T' dis E F).
Lemma tenso_qo S T S' T' (disS : [disjoint S & S']) (disT : [disjoint T & T']) 
  (E : 'QO[H]_(S,T)) (F : 'QO[H]_(S',T')) : tenso E F \is isqo.
Proof. 
rewrite [X in X :⊗ _](krausopE) [X in _ :⊗ X](krausopE) tenso_krausso//.
apply/krausso_qoP. rewrite /trace_nincr -tenf11 pair_bigV/=.
under eq_bigr do under eq_bigr do rewrite tenf_adj -(tenf_comp _ _ _ _ disT).
under eq_bigr do rewrite -linear_sumr/=.
rewrite -linear_suml/=. apply: lev_pbreg2=>//.
1,2: by rewrite sumv_ge0//==>i _; rewrite form_ge0.
all: apply: krausop_tn.
Qed.
Canonical tenso_qoType S T S' T' disS disT E F := QOType (@tenso_qo S T S' T' disS disT E F).
Lemma tenso_qc S T S' T' (disS : [disjoint S & S']) (disT : [disjoint T & T']) 
  (E : 'QC[H]_(S,T)) (F : 'QC[H]_(S',T')) : tenso E F \is isqc.
Proof. 
rewrite [X in X :⊗ _](krausopE) [X in _ :⊗ X](krausopE) tenso_krausso//.
apply/krausso_qcP. rewrite /trace_presv -tenf11 pair_bigV/=.
under eq_bigr do under eq_bigr do rewrite tenf_adj -(tenf_comp _ _ _ _ disT).
under eq_bigr do rewrite -linear_sumr/= qm_tpE.
by rewrite -linear_suml/= qm_tpE.
Qed.
Canonical tenso_qcType S T S' T' disS disT E F := QCType (@tenso_qc S T S' T' disS disT E F).

Lemma liftso_krausso S T (sub : S :<=: T) (F : finType) (f : F -> 'F[H]_S) :
  liftso sub (krausso f) = krausso (lift_fun sub f).
Proof.
rewrite /lift_lf /liftso -castso_krausso; f_equal.
by rewrite -formso1 tenso_krausso_formso// disjointXD.
Qed.
Lemma liftso_formso S T (sub : S :<=: T) (f : 'End('H[H]_S)) :
  liftso sub (formso f) = formso (lift_lf sub f).
Proof. by rewrite liftso_krausso. Qed.
Lemma liftso_cp S T (sub : S :<=: T) (E : 'CP[H]_S) :
  liftso sub E \is iscp.
Proof. by rewrite krausopE liftso_krausso cp_iscpP. Qed.
Canonical liftso_cpType S T sub E := CPType (@liftso_cp S T sub E).
Lemma liftso_qo S T (sub : S :<=: T) (E : 'QO[H]_S) :
  liftso sub E \is isqo.
Proof. by rewrite /liftso castso_qoE tenso_qo// disjointXD. Qed.
Canonical liftso_qoType S T sub E := QOType (@liftso_qo S T sub E).
Lemma liftso_qc S T (sub : S :<=: T) (E : 'QC[H]_S) :
  liftso sub E \is isqc.
Proof. by rewrite /liftso castso_qcE tenso_qc// disjointXD. Qed.
Canonical liftso_qcType S T sub E := QCType (@liftso_qc S T sub E).

Lemma liftso_is_linear S T (sub : S :<=: T) : linear (liftso sub).
Proof. by move=>a x y; rewrite /liftso linearPl/= linearP. Qed.
Canonical liftso_additive S T sub := Additive (@liftso_is_linear S T sub).
Canonical liftso_linear S T sub := Linear (@liftso_is_linear S T sub).

Lemma lift_lf_is_linear S T (sub : S :<=: T) : linear (lift_lf sub).
Proof. by move=>a x y; rewrite /lift_lf linearPl/= linearP. Qed.
Canonical lift_lf_additive S T sub := Additive (@lift_lf_is_linear S T sub).
Canonical lift_lf_linear S T sub := Linear (@lift_lf_is_linear S T sub).

Lemma lift_fun_tn S T (sub : S :<=: T) (F : finType) (f : 'TN[H]_(F;S)) :
  trace_nincr (lift_fun sub f).
Proof.
move: (qo_isqoP [QO of liftso sub (krausso f)])=>/=.
by rewrite liftso_krausso=>/krausso_qoP.
Qed.
Canonical lift_fun_tnType S T sub F f := TNType (@lift_fun_tn S T sub F f).

Lemma lift_fun_tp S T (sub : S :<=: T) (F : finType) (f : 'QM[H]_(F;S)) :
  trace_presv (lift_fun sub f).
Proof.
move: (qc_isqcP [QC of liftso sub (krausso f)])=>/=.
by rewrite liftso_krausso=>/krausso_qcP.
Qed.
Definition lift_fun_qm := lift_fun_tp.
Canonical lift_fun_tpType S T sub F f := TPType (@lift_fun_tp S T sub F f).

Lemma lift_lfE S T (sub : S :<=: T) (f: 'F[H]_S) :
  lift_lf sub f = castlf (setUD_sub sub, setUD_sub sub) (f \⊗ (\1 : 'F[H]_(T :\: S))).
Proof. by []. Qed.

Lemma lift_lf1 S T (sub : S :<=: T) : lift_lf sub (\1 : 'F[H]_S) = \1.
Proof. by rewrite /lift_lf tenf11 castlf1. Qed.

Lemma lift_lf_lef S T (sub : S :<=: T) (P Q: 'F[H]_S) :
  (lift_lf sub P ⊑ lift_lf sub Q) = (P ⊑ Q).
Proof.
by rewrite /lift_lf lef_cast -subv_ge0 -[RHS]subv_ge0 
  -linearBl/= ptenf_lge0// ?disjointXD// ltf01.
Qed.

Lemma lift_lf_inj S T (sub : S :<=: T) : injective (lift_lf sub).
Proof. by move=>P Q /eqP; rewrite eq_le !lift_lf_lef -eq_le=>/eqP. Qed.

Lemma lift_lf_cplmt S T (sub : S :<=: T) (P: 'F[H]_S) :
  lift_lf sub (P^⟂) = (lift_lf sub P)^⟂.
Proof. by rewrite /lift_lf tenfBl linearB/= tenf11 castlf1. Qed.

Lemma lift_lf_ge0 S T (sub : S :<=: T) (P: 'F[H]_S) : 
  (0 : 'F[H]_S) ⊑ P = ((0 : 'F[H]__) ⊑ lift_lf sub P).
Proof. by rewrite -(lift_lf_lef sub) linear0. Qed.

Lemma lift_lf_le1 S T (sub : S :<=: T) (P: 'F[H]_S) : 
  P ⊑ \1 = (lift_lf sub P ⊑ \1).
Proof. by rewrite -(lift_lf_lef sub) lift_lf1. Qed.

Lemma lift_lf_adj S T (sub : S :<=: T) (P: 'F[H]_S) :
  lift_lf sub (P^A) = (lift_lf sub P)^A.
Proof. by rewrite !lift_lfE  castlf_adj/= tenf_adj adjf1. Qed.

Lemma lift_lf_tr S T (sub : S :<=: T) (P: 'F[H]_S) :
  lift_lf sub (P^T) = (lift_lf sub P)^T.
Proof. by rewrite !lift_lfE  castlf_tr/= tenf_tr trf1. Qed.

Lemma lift_lf_conj S T (sub : S :<=: T) (P: 'F[H]_S) :
  lift_lf sub (P^C) = (lift_lf sub P)^C.
Proof. by rewrite !lift_lfE castlf_conj/= tenf_conj conjf1. Qed.

Lemma lift_lf_comp S T (sub : S :<=: T) (P Q: 'F[H]_S) :
  lift_lf sub (P \o Q) = lift_lf sub P \o lift_lf sub Q.
Proof. by rewrite !lift_lfE mul_cast -tenf_comp ?disjointXD// comp_lfun1l. Qed.

Lemma lift_lf_hermE S T (sub : S :<=: T) (P: 'F[H]_S) :
  P \is hermlf = (lift_lf sub P \is hermlf).
Proof.
by rewrite !hermlfE -lift_lf_adj; apply/eqb_iff; 
  split=>[/eqP->|/eqP/lift_lf_inj->].
Qed.

Lemma lift_lf_herm S T (sub : S :<=: T) (P : 'FH[H]_S) : lift_lf sub P \is hermlf.
Proof. by rewrite -lift_lf_hermE hermf_herm. Qed.
Canonical lift_lf_hermfType S T sub P := HermfType (@lift_lf_herm S T sub P).

Lemma lift_lf_psdE S T (sub : S :<=: T) (P: 'F[H]_S) :
  P \is psdlf = (lift_lf sub P \is psdlf).
Proof. rewrite !psdlfE; exact: lift_lf_ge0. Qed.

Lemma lift_lf_psd S T (sub : S :<=: T) (P : 'F+[H]_S) : lift_lf sub P \is psdlf.
Proof. by rewrite -lift_lf_psdE psdf_psd. Qed.
Canonical lift_lf_psdfType S T sub P := PsdfType (@lift_lf_psd S T sub P).

Lemma lift_lf_obsE S T (sub : S :<=: T) (P: 'F[H]_S) :
  P \is obslf = (lift_lf sub P \is obslf).
Proof. by rewrite !lef_obs -!(lift_lf_lef sub) linear0 lift_lf1. Qed.

Lemma lift_lf_obs S T (sub : S :<=: T) (P : 'FO[H]_S) : lift_lf sub P \is obslf.
Proof. by rewrite -lift_lf_obsE obsf_obs. Qed.
Canonical lift_lf_obsfType S T sub P := ObsfType (@lift_lf_obs S T sub P).

Lemma lift_lf_unitaryE S T (sub : S :<=: T) (U: 'F[H]_S) :
  U \is unitarylf = (lift_lf sub U \is unitarylf).
Proof.
apply/Bool.eq_iff_eq_true; split; move=>/unitarylfP PD; 
  apply/unitarylfP; move: PD; rewrite -lift_lf_adj -lift_lf_comp.
by move=>->; rewrite lift_lf1.
by rewrite -(lift_lf1 sub)=>/lift_lf_inj.
Qed.

Lemma lift_lf_unitary S T (sub : S :<=: T) (P : 'FU[H]_S) : lift_lf sub P \is unitarylf.
Proof. by rewrite -lift_lf_unitaryE unitaryf_unitary. Qed.
Canonical lift_lf_unitaryfType S T sub P := UnitaryfType (@lift_lf_unitary S T sub P).

Lemma lift_lf_projE S T (sub : S :<=: T) (P: 'F[H]_S) :
  P \is projlf = (lift_lf sub P \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP[P1 P2]; apply/projlfP;
move: P1 P2; rewrite -lift_lf_adj -lift_lf_comp.
by move=>->->. by move=>/lift_lf_inj+/lift_lf_inj.
Qed.

Lemma lift_lf_proj S T (sub : S :<=: T) (P : 'FP[H]_S) : lift_lf sub P \is projlf.
Proof. by rewrite -lift_lf_projE projf_proj. Qed.
Canonical lift_lf_projfType S T sub P := ProjfType (@lift_lf_proj S T sub P).

Lemma lift_lf2 S T W (sub1 : S :<=: T) (sub2 : T :<=: W) (f : 'F[H]_S) :
  lift_lf sub2 (lift_lf sub1 f) = lift_lf (fintype.subset_trans sub1 sub2) f.
Proof.
rewrite /lift_lf castlf_out; apply/cf_eq; rewrite !cf_castK -tenfA tenf11.
apply/cf_tens=>//; apply/cf_implicit1; move: sub1 sub2; fsetdec L.
Qed.

Lemma lift_lf_tenf1r S T W (sub : S :|: T :<=: W) (f : 'F[H]_S) :
  [disjoint S & T] ->
  lift_lf sub (f \⊗ \1) = lift_lf (fintype.subset_trans (subsetUl _ _) sub) f.
Proof.
move=>dis; rewrite /lift_lf; apply/cf_eq; rewrite !cf_castK -tenfA tenf11.
apply/cf_tens=>//; apply/cf_implicit1; apply/setP=>x.
move: sub dis; rewrite subsets_disjoint -!setI_eq0=>/eqP/setP/(_ x)+/eqP/setP/(_ x).
by rewrite !inE; case: (x \in S); case: (x \in T); case: (x \in W).
Qed.

Lemma lift_lf_tenf1l S T W (sub : S :|: T :<=: W) (f : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf sub (\1 \⊗ f) = lift_lf (fintype.subset_trans (subsetUr _ _) sub) f.
Proof.
move=>dis; rewrite /lift_lf; apply/cf_eq; rewrite !cf_castK -tenfA tenfC -tenfA tenf11.
apply/cf_tens=>//; apply/cf_implicit1; apply/setP=>x.
move: sub dis; rewrite subsets_disjoint -!setI_eq0=>/eqP/setP/(_ x)+/eqP/setP/(_ x).
by rewrite !inE; case: (x \in S); case: (x \in T); case: (x \in W).
Qed.

Lemma setUDlid S T : [disjoint S & T] -> (S :|: T) :\: S = T.
Proof. 
by move=>dis; rewrite setDUl setDv set0U; apply/setDidPl; rewrite disjoint_sym.
Qed.

Lemma setUDrid S T : [disjoint S & T] -> (S :|: T) :\: T = S.
Proof. 
by move=>dis; rewrite setDUl setDv setU0; apply/setDidPl.
Qed.

Lemma lift_lfEl S T (f : 'F[H]_S) :
  [disjoint S & T] -> lift_lf (subsetUl S T) f = f \⊗ \1.
Proof.
move=>dis; rewrite /lift_lf.
move: (setUD_sub (subsetUl S T)) (esym (setUDlid dis))=>+P1.
by case: ((S :|: T) :\: S) / P1=>P1; rewrite castlf_id.
Qed.

Lemma lift_lfEr S T (f : 'F[H]_T) :
  [disjoint S & T] -> lift_lf (subsetUr S T) f = \1 \⊗ f.
Proof.
move=>dis; rewrite /lift_lf.
move: (setUD_sub (subsetUr S T)) (esym (setUDrid dis))=>+P1.
by case: ((S :|: T) :\: T) / P1=>P1; rewrite -tenf_castC castlf_comp castlf_id.
Qed.

Lemma lift_lf_UC S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf (subsetUl S T) f \o lift_lf (subsetUr S T) g = 
  lift_lf (subsetUr S T) g \o lift_lf (subsetUl S T) f.
Proof.
by move=>dis; rewrite lift_lfEl// lift_lfEr// -!tenf_comp// !comp_lfun1l !comp_lfun1r.
Qed.

Lemma lift_lf_compT S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf (subsetUl S T) f \o lift_lf (subsetUr S T) g = f \⊗ g.
Proof.
by move=>dis; rewrite lift_lfEl// lift_lfEr// -!tenf_comp// !comp_lfun1l !comp_lfun1r.
Qed.

Lemma lift_lf_compC S T W (sub1 : S :<=: W) (sub2 : T :<=: W) (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf sub1 f \o lift_lf sub2 g = lift_lf sub2 g \o lift_lf sub1 f.
Proof.
move=>dis. move: (subUsetPP sub1 sub2)=>P1.
rewrite (eq_irrelevance sub1 (fintype.subset_trans (subsetUl S T) P1)) 
(eq_irrelevance sub2 (fintype.subset_trans (subsetUr S T) P1)).
by rewrite -!lift_lf2 -!lift_lf_comp lift_lf_UC.
Qed.

Lemma lift_lf_sdot S T W (sub1 : S :<=: W) (sub2 : T :<=: W) (P : 'F[H]_S) (Q : 'F[H]_T) :
  lift_lf (subUsetPP sub1 sub2) (P \O Q) = lift_lf sub1 P \o lift_lf sub2 Q.
Proof.
rewrite /lift_lf -{1}(comp_lfun1l \1) /sdot_lfun /dot_lfun -(mul_cast _ _ erefl).
rewrite tenf_comp; last first.
apply/cf_eq; rewrite !cf_castK; apply/cf_comp; rewrite ?castlf_comp castlf_out 
  !cf_castK -tenfA tenf11; apply/cf_tens=>//; apply/cf_implicit1.
all: move: sub1 sub2; fsetdec L.
Qed.

Lemma liftsoE S T (sub : S :<=: T) (f: 'SO[H]_S) :
  liftso sub f = castso (setUD_sub sub, setUD_sub sub) (f :⊗ :1).
Proof. by []. Qed.

Lemma liftsoEf S T (sub : S :<=: T) (E : 'SO[H]_S) (x : 'F_S) :
  liftso sub E (lift_lf sub x) = lift_lf sub (E x).
Proof.
rewrite /liftso /lift_lf castsoE/= castlf_comp castlf_id.
by rewrite -tenso_correct ?disjointXD ?soE.
Qed.

Lemma liftso1 S T (sub : S :<=: T) : liftso sub :1 = :1.
Proof. by rewrite /liftso tenso11 castso1. Qed.

Lemma leso01 (U : chsType) : (0 : 'SO) ⊑ (:1 : 'SO(U)). Proof. by apply/cpgeso0. Qed.
Lemma qc_neq0 (U V: chsType) (E : 'QC(U,V)) : (E : 'SO) != 0.
Proof.
apply/eqP=>P; move: P=>/(f_equal (@dualso _ _))/superopP/(_ \1)/eqP.
by rewrite dualso0 dual_qc1_eq1 soE oner_eq0.
Qed.
Lemma qc_gt0 (U V: chsType) (E : 'QC(U,V)) : (0 : 'SO) ⊏ E.
Proof. by rewrite lt_def qc_neq0 cpgeso0. Qed.
Lemma idso_neq0 (U : chsType) : (:1 : 'SO(U)) != 0. Proof. exact: qc_neq0. Qed.
Lemma ltso01 (U : chsType) : (0 : 'SO(U)) ⊏ :1. Proof. exact: qc_gt0. Qed.

Lemma tenso_ge0 S T (f : 'SO[H]_S) (g : 'SO[H]_T) :
  [disjoint S & T] -> (0 :'SO) ⊑ f -> (0 :'SO) ⊑ g -> (0 :'SO) ⊑ f :⊗ g.
Proof.
move=>P1 /leso0_cpP Pf /leso0_cpP Pg; apply/leso0_cpP.
move: (tenso_cp P1 (CPType Pf) (CPType Pg))=>//.
Qed.

Lemma so_neq0P (U V : chsType) (E : 'SO(U,V)) : 
  reflect (exists f, E f != 0) (E != 0).
Proof.
apply/(iffP negP); rewrite not_existsP; apply contra_not.
by move=>P; apply/eqP/superopP=>u; move: (P u)=>/negP; rewrite negbK soE=>/eqP.
by move=>/eqP-> x; rewrite soE/= eqxx.
Qed.

Lemma tenso_eq0 S T (dis : [disjoint S & T]) (f : 'SO[H]_S) (g : 'SO[H]_T) :
  f :⊗ g == 0 = (f == 0) || (g == 0).
Proof.
apply/Bool.eq_iff_eq_true; split.
move=>/eqP/superopP P1. case: eqP=>//=; move=>/eqP/so_neq0P[v /negPf Pv].
apply/eqP/superopP=>x; move: (P1 (v \⊗ x))=>/eqP.
by rewrite -tenso_correct// !soE tenf_eq0// Pv/==>/eqP.
by move=>/orP[/eqP->|/eqP->]; rewrite ?linear0l ?linear0r eqxx.
Qed.

Lemma psdlf_decomp (U : chsType) (f : 'End(U)): f \is psdlf -> 
  exists (v : 'I_(Vector.dim U) -> U), f = \sum_i [> v i ; v i <].
Proof.
rewrite qualifE=>/diag_decomp_absorb.
set v := fun k => sqrtC (spectral_diag (f2mx f) 0 k) *: row k (spectralmx (f2mx f)).
rewrite/==>P. exists (fun k=> r2v (v k)).
apply/f2mx_inj; rewrite P linear_sum/=; apply eq_bigr=>i _.
by rewrite r2vK.
Qed.

Lemma ge0_krausE (U V : chsType) (E : 'SO(U,V)) x : (0:'SO) ⊑ E ->
  E x = \sum_i ((krausop E i) \o x \o (krausop E i)^A)%VF.
Proof. by move=>/leso0_cpP P; move: (krausE (CPType P) x). Qed.

(* tenf_cast1l *)

Lemma gtf0_trlfP (U : chsType) (x : 'End(U)) :
  reflect (0%:VF ⊑ x /\ \Tr x > 0) (0%:VF ⊏ x).
Proof.
rewrite [_ ⊏ x]lt_def; apply/(iffP andP)=>[[P1 P2]|[P1 P2]]; split=>//; last first.
move: P2; apply/contraTN=>/eqP->; by rewrite linear0 ltxx.
rewrite lt_def psdlf_trlf ?psdlfE// andbT; move: P1; apply/contraNN=>/eqP.
rewrite lftrace_baseE=>P4. move: (ge0_form P2)=>[g Pg].
have P3 : forall i, true -> (fun i=>[< eb i; x (eb i) >]) i = 0.
by apply: psumr_eq0P=>// i _; rewrite Pg lfunE adj_dotEV/= ge0_dotp.
suff: g = 0 by rewrite Pg=>->; rewrite comp_lfun0r.
apply/(intro_onb eb_onbasis)=>i/=; rewrite lfunE/=; apply/eqP.
by rewrite -dotp_eq0 -adj_dotEV -comp_lfunE -Pg; apply/eqP/P3.
Qed.

Lemma ptenso_rge0 S T (dis : [disjoint S & T]) (x : 'SO[H]_S) (y : 'SO[H]_T) :
  (0 : 'SO) ⊏ x -> ((0 : 'SO) ⊑ x :⊗ y) = ((0 : 'SO) ⊑ y).
Proof.
rewrite lt_def=>/andP[/so_neq0P[f /eqP Pf] xge0]; 
rewrite -eqb_iff; split; last by apply: tenso_ge0.
have : exists v : 'H_S, x [> v ; v <] != 0.
  rewrite not_existsP=>P.
  have P0 v : x [> v ; v <] = 0.
  by move: (P v)=>/negP; rewrite negbK=>/eqP.
  apply Pf; move: (lf_psd_decomp f)=>[M1[M2[M3[M4]]]][]/psdlf_decomp[v1 P1]
    []/psdlf_decomp[v2 P2][]/psdlf_decomp[v3 P3][]/psdlf_decomp[v4 P4]->.
  rewrite linearB/= linearD/= linearB/= !linearZ/=.
  suff ->: x M1 = 0. suff ->: x M2 = 0. suff ->: x M3 = 0. suff ->: x M4 = 0.
  by rewrite oppr0 scaler0 !addr0.
  1: rewrite P4. 2: rewrite P3. 3: rewrite P2. 4: rewrite P1.
  1,2,3,4: by rewrite linear_sum/= big1.
move=>[v Pv] xyge0.
pose K i := castlf (set0U T, set0U T) ((v2df (deltav i.2) \⊗ \1) 
  \o (krausop (x :⊗ y) i.1) \o (v2f v \⊗ \1)).
pose c := sqrtC (\Tr (x [> v ; v <])).
have P6: 0%:VF ⊏ x [> v; v <].
  rewrite lt_def Pv/=; move: xge0=>/(leso0_cpP) P5.
  by move: (@cp_ge0 _ _ (CPType P5) _ (outp_ge0 v)).
have cgt0 : c > 0 by rewrite /c sqrtC_gt0; move: P6=>/gtf0_trlfP[].
move: (lt0r_neq0 cgt0)=> cneq0.
suff ->: y = krausso (fun i=>c^-1 *: (K i)) by apply/leso0_cpP/cp_iscpP.
apply/superopP=>z; rewrite -{2}(tenf_cast1l z) kraussoE.
under eq_bigr do rewrite adjfZ !linearZl linearZr/= scalerA.
rewrite -linear_sum/= geC0_conj ?invr_ge0; first by apply/ltW.
apply: (@scalerI _ _ (c^+2) _); first by apply/expf_neq0.
rewrite scalerA mulrA expr2 mulfK// mulfV// scale1r -expr2 sqrtCK.
rewrite -[LHS]tenf_cast1l tenfZr -tenfZl.
have ->: \Tr (x [> v; v <]) *: \1 = \sum_i ((v2df (deltav i))\o(x [> v; v <])\o(v2f (deltav i))).
  rewrite (onb_trlf deltav_onbasis)/= scaler_suml; apply eq_bigr=>i _.
  apply/lfunP=>u; rewrite !lfunE/= [RHS]lfunE/= v2dfE lfunE/= v2fE linearZ/= linearZ/=.
  by apply/sv2s_inj; rewrite s2svK linearZ/= mulrC.
rewrite linear_suml/= linear_sum/= pair_bigV/= exchange_big/=; apply eq_bigr=>i _.
under eq_bigr do rewrite /K/= castlf_adj/= !mul_cast !adjf_comp !comp_lfunA.
rewrite -linear_sum/=; f_equal; rewrite -linear_suml/=.
under eq_bigr do rewrite -!comp_lfunA; rewrite -linear_sumr/=.
suff ->: (\sum_i0 (krausop (x :⊗ y) i0 \o (v2f v \⊗ \1 \o (\1 \⊗ z \o 
  ((v2f v \⊗ \1)^A \o (krausop (x :⊗ y) i0)^A))))) = (x :⊗ y) ([> v; v<] \⊗ z).
  by rewrite -tenso_correct// tenf_adj -!tenf_comp// 
  v2df_adj comp_lfun1l adjf1 comp_lfun1r.
rewrite [RHS]ge0_krausE//; apply eq_bigr=>j _; rewrite !comp_lfunA.
by f_equal; rewrite -!comp_lfunA; f_equal; rewrite tenf_adj adjf1 -!tenf_comp 
  ?disjoint0X// !comp_lfun1l v2f_adj comp_out comp_lfun1r.
Qed.

Lemma tenso_castC S T S' T' (f: 'SO[H]_(S,T)) (g: 'SO[H]_(S',T')) : 
  castso ((setUC S S'), (setUC T T')) (f :⊗ g) = (g :⊗ f).
Proof.
apply/superopPD=>i j; rewrite castsoE/= castlf_outp/= 
  !deltav_cast -!tensodf tenf_castC; do ? f_equal.
all: by rewrite idxSl_idxR idxSr_idxR idxR_castR ?subsetUl ?subsetUr// =>P;
  rewrite [X in _ = idxR X _](eq_irrelevance _ P).
Qed.

Lemma ptenso_lge0 S T (dis : [disjoint S & T]) (y : 'SO[H]_T) (x : 'SO[H]_S) :
  (0 : 'SO) ⊏ y -> ((0 : 'SO) ⊑ x :⊗ y) = ((0 : 'SO) ⊑ x).
Proof.
by move=>Q; rewrite -tenso_castC leso_cast_symV linear0 ptenso_rge0// disjoint_sym.
Qed.

Definition tenso_bregVOrderMixin S T dis := 
    bregVOrderMixin (@tenso_eq0 S T dis) (ptenso_rge0 dis) (ptenso_lge0 dis).
Canonical tenso_bregVOrderType S T dis := 
  bregVOrderType (@tenso _ _ S S T T) (@tenso_bregVOrderMixin S T dis).

Lemma ptenso_rgt0 S T (dis : [disjoint S & T]) (x : 'SO[H]_S) (y : 'SO[H]_T) :
  (0 : 'SO) ⊏ x -> ((0 : 'SO) ⊏ x :⊗ y) = ((0 : 'SO) ⊏ y).
Proof. exact: pbregv_rgt0. Qed.

Lemma ptenso_lgt0 S T (dis : [disjoint S & T]) (y : 'SO[H]_T) (x : 'SO[H]_S) :
  (0 : 'SO) ⊏ y -> ((0 : 'SO) ⊏ x :⊗ y) = ((0 : 'SO) ⊏ x).
Proof. exact: pbregv_lgt0. Qed.

Lemma liftso_leso S T (sub : S :<=: T) (P Q: 'SO[H]_S) :
  P ⊑ Q = (liftso sub P ⊑ liftso sub Q).
Proof.
by rewrite /liftso leso_cast -subv_ge0 -[RHS]subv_ge0 
  -linearBl/= ptenso_lge0// ?disjointXD// ltso01.
Qed.

Lemma liftso_inj S T (sub : S :<=: T) : injective (liftso sub).
Proof. by move=>P Q /eqP; rewrite eq_le -!liftso_leso -eq_le=>/eqP. Qed.

Lemma liftso_ge0 S T (sub : S :<=: T) (P: 'SO[H]_S) : 
  (0 : 'SO) ⊑ P = ((0 : 'SO) ⊑ liftso sub P).
Proof. by rewrite (liftso_leso sub) linear0. Qed.

Lemma liftso_le1 S T (sub : S :<=: T) (P: 'SO[H]_S) : 
  P ⊑ :1 = (liftso sub P ⊑ :1).
Proof. by rewrite (liftso_leso sub) liftso1. Qed.

Lemma liftso_dual S T (sub : S :<=: T) (P: 'SO[H]_S) : 
  (liftso sub P)^*o = liftso sub P^*o.
Proof. by rewrite /liftso castso_dual/= tenso_dual dualso1. Qed.

Lemma liftso_comp S T (sub : S :<=: T) (P Q: 'SO[H]_S) :
  liftso sub (P :o Q) = liftso sub P :o liftso sub Q.
Proof. by rewrite /liftso compso_cast -tenso_comp ?disjointXD ?comp_so1l//. Qed.

Lemma liftso_compr S T (sub : S :<=: T) (P Q: 'SO[H]_S) :
  liftso sub (P o: Q) = liftso sub P o: liftso sub Q.
Proof. by rewrite !comp_soErl liftso_comp. Qed.

Lemma liftsoEl S T (f : 'SO[H]_S) :
  [disjoint S & T] -> liftso (subsetUl S T) f = f :⊗ :1.
Proof.
move=>dis; rewrite /liftso.
move: (setUD_sub (subsetUl S T)) (esym (setUDlid dis))=>+P1.
by case: ((S :|: T) :\: S) / P1=>P1; rewrite castso_id.
Qed.

Lemma liftsoEr S T (f : 'SO[H]_T) :
  [disjoint S & T] -> liftso (subsetUr S T) f = :1 :⊗ f.
Proof.
move=>dis; rewrite /liftso.
move: (setUD_sub (subsetUr S T)) (esym (setUDrid dis))=>+P1.
by case: ((S :|: T) :\: T) / P1=>P1; rewrite -tenso_castC castso_comp castso_id.
Qed.

Lemma liftso_UC S T (f : 'SO[H]_S) (g : 'SO[H]_T) :
  [disjoint S & T] ->
  liftso (subsetUl S T) f :o liftso (subsetUr S T) g = 
  liftso (subsetUr S T) g :o liftso (subsetUl S T) f.
Proof.
by move=>dis; rewrite liftsoEl ?liftsoEr -?tenso_comp ?comp_so1l ?comp_so1r.
Qed.

Lemma tenso_castA S1 T1 S2 T2 S3 T3 (f: 'SO[H]_(S1,T1)) (g: 'SO[H]_(S2,T2))
  (h: 'SO[H]_(S3,T3)) : 
 castso (setUA S1 S2 S3, setUA T1 T2 T3) (f :⊗ (g :⊗ h)) = ((f :⊗ g) :⊗ h).
Proof.
apply/superopPD=>i j; rewrite castsoE/= castlf_outp/= 
  !deltav_cast -!tensodf tenf_castA; do ? f_equal;
do ? [apply f_equal2 | apply f_equal] =>//; 
rewrite ?idxSl_idxR ?idxSr_idxR ?idxR_castR -?setUA ?subsetUl ?subsetUr// => H1; 
rewrite !idxRA; by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenso_castl S1 T1 S2 T2 S1' T1' (A : 'SO[H]_(S1,T1)) (B : 'SO[H]_(S2,T2)) 
  (eqA : (S1 = S1') * (T1 = T1')) :
  castso eqA A :⊗ B = castso (setcTl _ eqA.1, setcTl _ eqA.2) (A :⊗ B).
Proof. by case: eqA=>P1 P2; case: S1' / P1; case: T1' / P2=>/=; rewrite !castso_id. Qed.

Lemma tenso_castr S1 T1 S2 T2 S1' T1' (A : 'SO[H]_(S1,T1)) (B : 'SO[H]_(S2,T2)) 
  (eqA : (S1 = S1') * (T1 = T1')) :
  B :⊗ castso eqA A = castso (setcTr _ eqA.1, setcTr _ eqA.2) (B :⊗ A).
Proof. by case: eqA=>P1 P2; case: S1' / P1; case: T1' / P2=>/=; rewrite !castso_id. Qed.

Lemma liftso2 S T W (sub1 : S :<=: T) (sub2 : T :<=: W) (f : 'SO[H]_S) :
  liftso sub2 (liftso sub1 f) = liftso (fintype.subset_trans sub1 sub2) f.
Proof.
rewrite /liftso tenso_castl -tenso_castA tenso11.
apply/castso_symV. rewrite !castso_comp/=.
suff P1 : (T :\: S :|: W :\: T) = W :\: S.
have P2: S :|: (T :\: S :|: W :\: T) = S :|: W :\: S by rewrite P1.
rewrite (eq_irrelevance (etrans _ _) P2).
by case: (W :\: S) / P1 P2=>P2; rewrite castso_id.
move: sub1 sub2; fsetdec L.
Qed.

Lemma liftso_compC S T W (sub1 : S :<=: W) (sub2 : T :<=: W) (f : 'SO[H]_S) (g : 'SO[H]_T) :
  [disjoint S & T] ->
  liftso sub1 f :o liftso sub2 g = liftso sub2 g :o liftso sub1 f.
Proof.
move=>dis. move: (subUsetPP sub1 sub2)=>P1.
rewrite (eq_irrelevance sub1 (fintype.subset_trans (subsetUl S T) P1)) 
(eq_irrelevance sub2 (fintype.subset_trans (subsetUr S T) P1)).
by rewrite -!liftso2 -!liftso_comp liftso_UC.
Qed.

Lemma lift_fun2 S T W (sub1 : S :<=: T) (sub2 : T :<=: W) (F : finType) (f : F -> 'F[H]_S) :
  lift_fun sub2 (lift_fun sub1 f) = lift_fun (fintype.subset_trans sub1 sub2) f.
Proof. by rewrite /lift_fun; apply/funext=>i; rewrite lift_lf2. Qed.

Lemma lift_lf_id S (sub : S :<=: S) (f : 'F[H]_S) :
  lift_lf sub f = f.
Proof. 
by apply/(@lift_lf_inj _ _ sub); rewrite lift_lf2 (eq_irrelevance (_ sub sub) sub).
Qed.

Lemma liftso_id S (sub : S :<=: S) (E : 'SO[H]_S) :
  liftso sub E = E.
Proof. 
by apply/(@liftso_inj _ _ sub); rewrite liftso2 (eq_irrelevance (_ sub sub) sub).
Qed.

Lemma lift_fun_id S (sub : S :<=: S) (F : finType) (f : F -> 'F[H]_S) :
  lift_fun sub f = f.
Proof. by rewrite /lift_fun; apply/funext=>i; rewrite lift_lf_id. Qed. 

Lemma liftso_elemso S T (sub : S :<=: T) (F : finType) (M : F -> 'F[H]_S) i :
  liftso sub (elemso M i) = elemso (lift_fun sub M) i.
Proof. exact: liftso_formso. Qed.

Lemma liftso_ifso S T (sub : S :<=: T) (F : finType) (M : F -> 'F[H]_S) 
  (br : F -> 'SO[H]_S) :
  liftso sub (ifso M br) = ifso (lift_fun sub M) (fun i => liftso sub (br i)).
Proof.
rewrite !ifso_elem linear_sum/=; apply eq_bigr=>i _.
by rewrite liftso_comp liftso_elemso.
Qed.

Import HermitianTopology.Exports.
Lemma liftso_whileso S T (sub : S :<=: T) (M : 'TN[H]_(bool;S)) b (D : 'QO[H]_S) :
  liftso sub (whileso M b D) = whileso (lift_fun sub M) b (liftso sub D).
Proof.
rewrite /whileso -linear_lim. apply: whileso_is_cvg.
suff ->: (liftso_linear sub \o whileso_iter M b D)%FUN = 
  whileso_iter (lift_fun sub M) b (liftso sub D) by [].
apply/funext=>i/=; rewrite !whileso_iter_incrE liftso_comp liftso_elemso; f_equal.
rewrite linear_sum/=; apply eq_bigr=>j _; case: j=>/= m _.
elim: m=>[|m IH]; first by rewrite /=liftso1.
by rewrite !whileso_incrE !liftso_comp liftso_elemso IH.
Qed.

End SOTensorTheory.

Section LiftFullSpace.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W: {set L}).

Local Notation sub S := (@subsetT L S).
Lemma subsetTE S : all_equal_to (sub S).
Proof. by move=>x; rewrite /= (eq_irrelevance x (sub S)). Qed.

Definition liftf_lf S f : 'F[H]_setT := lift_lf (sub S) f.
Definition liftfso S E : 'SO[H]_setT := liftso (sub S) E.
Definition liftf_fun S (F : finType) (f : F -> 'F[H]_S) := lift_fun (sub S) f.

Lemma liftf_funE S (F : finType) (f : F -> 'F[H]_S) : 
  liftf_fun f = (fun i=> liftf_lf (f i)).
Proof. by []. Qed.

Lemma liftfso_krausso S (F : finType) (f : F -> 'F[H]_S) :
  liftfso (krausso f) = krausso (liftf_fun f).
Proof. exact: liftso_krausso. Qed.
Lemma liftfso_formso S (f : 'End('H[H]_S)) :
  liftfso (formso f) = formso (liftf_lf f).
Proof. exact: liftso_formso. Qed.
Lemma liftfso_cp S (E : 'CP[H]_S) : liftfso E \is iscp. Proof. exact: liftso_cp. Qed.
Canonical liftfso_cpType S E := CPType (@liftfso_cp S E).
Lemma liftfso_qo S (E : 'QO[H]_S) : liftfso E \is isqo. Proof. exact: liftso_qo. Qed.
Canonical liftfso_qoType S E := QOType (@liftfso_qo S E).
Lemma liftfso_qc S (E : 'QC[H]_S) : liftfso E \is isqc. Proof. exact: liftso_qc. Qed.
Canonical liftfso_qcType S E := QCType (@liftfso_qc S E).

Lemma liftfso_is_linear S : linear (@liftfso S). Proof. exact: linearP. Qed.
Canonical liftfso_additive S := Additive (@liftfso_is_linear S).
Canonical liftfso_linear S := Linear (@liftfso_is_linear S).

Lemma liftf_lf_is_linear S : linear (@liftf_lf S). Proof. exact: linearP. Qed.
Canonical liftf_lf_additive S := Additive (@liftf_lf_is_linear S).
Canonical liftf_lf_linear S := Linear (@liftf_lf_is_linear S).

Lemma liftf_fun_tn S (F : finType) (f : 'TN[H]_(F;S)) : trace_nincr (liftf_fun f).
Proof. exact: lift_fun_tn. Qed.
Canonical liftf_fun_tnType S F f := TNType (@liftf_fun_tn S F f).

Lemma liftf_fun_tp S (F : finType) (f : 'QM[H]_(F;S)) : trace_presv (liftf_fun f).
Proof. exact: lift_fun_tp. Qed.
Definition liftf_fun_qm := liftf_fun_tp.
Canonical liftf_fun_tpType S F f := TPType (@liftf_fun_tp S F f).

Lemma liftf_lfE S (f: 'F[H]_S) :
  liftf_lf f = castlf (setUCr S, setUCr S) (f \⊗ (\1 : 'F[H]_(~:S))).
Proof.
rewrite /liftf_lf /lift_lf; move: (setUCr S) (setTD S)=>P1 P2.
by case: (~:S) / P2 P1=>P1; rewrite (eq_irrelevance (_ (sub _)) P1).
Qed.

Lemma liftf_lf1 S : liftf_lf (\1 : 'F[H]_S) = \1. Proof. exact: lift_lf1. Qed.
Lemma liftf_lf_inj S : injective (@liftf_lf S). Proof. exact: lift_lf_inj. Qed.

Lemma liftf_lf_lef S (P Q: 'F[H]_S) : (liftf_lf P ⊑ liftf_lf Q) = (P ⊑ Q).
Proof. exact: lift_lf_lef. Qed.
Lemma liftf_lf_cplmt S (P: 'F[H]_S) : liftf_lf (P^⟂) = (liftf_lf P)^⟂.
Proof. exact: lift_lf_cplmt. Qed.
Lemma liftf_lf_ge0 S (P: 'F[H]_S) : (0 : 'F[H]_S) ⊑ P = ((0 : 'F[H]__) ⊑ liftf_lf P).
Proof. exact: lift_lf_ge0. Qed.
Lemma liftf_lf_le1 S (P: 'F[H]_S) : P ⊑ \1 = (liftf_lf P ⊑ \1).
Proof. exact: lift_lf_le1. Qed.
Lemma liftf_lf_adj S (P: 'F[H]_S) : liftf_lf (P^A) = (liftf_lf P)^A.
Proof. exact: lift_lf_adj. Qed.
Lemma liftf_lf_tr S (P: 'F[H]_S) : liftf_lf (P^T) = (liftf_lf P)^T.
Proof. exact: lift_lf_tr. Qed.
Lemma liftf_lf_conj S (P: 'F[H]_S) : liftf_lf (P^C) = (liftf_lf P)^C.
Proof. exact: lift_lf_conj. Qed.
Lemma liftf_lf_comp S (P Q: 'F[H]_S) : liftf_lf (P \o Q) = liftf_lf P \o liftf_lf Q.
Proof. exact: lift_lf_comp. Qed.

Lemma liftf_lf_hermE S (P: 'F[H]_S) : P \is hermlf = (liftf_lf P \is hermlf).
Proof. exact: lift_lf_hermE. Qed.
Lemma liftf_lf_herm S (P : 'FH[H]_S) : liftf_lf P \is hermlf.
Proof. exact: lift_lf_herm. Qed.
Canonical liftf_lf_hermfType S P := HermfType (@liftf_lf_herm S P).
Lemma liftf_lf_psdE S (P: 'F[H]_S) : P \is psdlf = (liftf_lf P \is psdlf).
Proof. exact: lift_lf_psdE. Qed.
Lemma liftf_lf_psd S (P : 'F+[H]_S) : liftf_lf P \is psdlf.
Proof. exact: lift_lf_psd. Qed.
Canonical liftf_lf_psdfType S P := PsdfType (@liftf_lf_psd S P).
Lemma liftf_lf_obsE S (P: 'F[H]_S) : P \is obslf = (liftf_lf P \is obslf).
Proof. exact: lift_lf_obsE. Qed.
Lemma liftf_lf_obs S (P : 'FO[H]_S) : liftf_lf P \is obslf.
Proof. exact: lift_lf_obs. Qed.
Canonical liftf_lf_obsfType S P := ObsfType (@liftf_lf_obs S P).
Lemma liftf_lf_unitaryE S (U: 'F[H]_S) : U \is unitarylf = (liftf_lf U \is unitarylf).
Proof. exact: lift_lf_unitaryE. Qed.
Lemma liftf_lf_unitary S (P : 'FU[H]_S) : liftf_lf P \is unitarylf.
Proof. exact: lift_lf_unitary. Qed.
Canonical liftf_lf_unitaryfType S P := UnitaryfType (@liftf_lf_unitary S P).
Lemma liftf_lf_projE S (P: 'F[H]_S) : P \is projlf = (liftf_lf P \is projlf).
Proof. exact: lift_lf_projE. Qed.
Lemma liftf_lf_proj S (P : 'FP[H]_S) : liftf_lf P \is projlf.
Proof. exact: lift_lf_proj. Qed.
Canonical liftf_lf_projfType S P := ProjfType (@liftf_lf_proj S P).

Lemma liftf_lf2 S T (sub : S :<=: T) (f : 'F[H]_S) :
  liftf_lf (lift_lf sub f) = liftf_lf f.
Proof. by rewrite /liftf_lf lift_lf2 subsetTE. Qed.
Lemma liftf_lfid S (f : 'F[H]_S) : liftf_lf (liftf_lf f) = liftf_lf f.
Proof. exact: liftf_lf2. Qed.

Lemma liftf_lf_tenf1r S T (f : 'F[H]_S) :
  [disjoint S & T] -> liftf_lf (f \⊗ (\1 : 'F_T)) = liftf_lf f.
Proof. by move=>dis; rewrite /liftf_lf lift_lf_tenf1r// subsetTE. Qed.

Lemma liftf_lf_tenf1l S T (f : 'F[H]_T) :
  [disjoint S & T] -> liftf_lf ((\1 : 'F_S) \⊗ f) = liftf_lf f.
Proof. by move=>dis; rewrite /liftf_lf lift_lf_tenf1l// subsetTE. Qed.

Lemma liftf_lf_compC S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] -> liftf_lf f \o liftf_lf g = liftf_lf g \o liftf_lf f.
Proof. exact: lift_lf_compC. Qed.

Lemma liftf_lf_sdot S T (P: 'F[H]_S) (Q: 'F[H]_T) : 
  liftf_lf (P \O Q) = liftf_lf P \o liftf_lf Q.
Proof. by rewrite -lift_lf_sdot subsetTE. Qed.

Lemma liftf_lf2_tensl S T W (sub : S :<=: T) (P : 'F[H]_S) (R : 'F[H]_W):
  [disjoint T & W] ->
  liftf_lf (lift_lf sub P \⊗ R) = liftf_lf (P \⊗ R).
Proof.
move=>dis; rewrite /liftf_lf /lift_lf; apply/cf_eq.
rewrite !castlf_out !cf_castK -!tenfA; apply/cf_tens=>//. 
rewrite tenfC -tenfA tenf11; apply/cf_tens=>//; apply/cf_implicit1/setP=>x.
move: sub dis=>/setIidPr/setP/(_ x)+/setDidPl/setP/(_ x).
by rewrite !inE; case: (x \in S); case: (x \in T); case: (x \in W).
Qed.

Lemma liftf_lf2_tensr S T W (sub : S :<=: T) (P : 'F[H]_S) (R : 'F[H]_W):
  [disjoint T & W] ->
  liftf_lf (R \⊗ lift_lf sub P) = liftf_lf (R \⊗ P).
Proof.
move=>dis; rewrite /liftf_lf /lift_lf; apply/cf_eq.
rewrite !castlf_out !cf_castK -!tenfA; apply/cf_tens=>//. 
rewrite -tenfA tenf11; apply/cf_tens=>//; apply/cf_implicit1/setP=>x.
move: sub dis=>/setIidPr/setP/(_ x)+/setDidPl/setP/(_ x).
by rewrite !inE; case: (x \in S); case: (x \in T); case: (x \in W).
Qed.

Lemma liftfsoE S (f: 'SO[H]_S) : liftfso f = castso (setUCr S, setUCr S) (f :⊗ :1).
Proof.
rewrite /liftfso /liftso; move: (setUCr S) (setTD S)=>P1 P2.
by case: (~:S) / P2 P1=>P1; rewrite (eq_irrelevance (_ (sub _)) P1).
Qed.

Lemma liftfsoEf S (E : 'SO[H]_S) (x : 'F_S) : liftfso E (liftf_lf x) = liftf_lf (E x).
Proof. exact: liftsoEf. Qed.
Lemma liftfso1 S : liftfso (:1 : 'SO[H]_S) = :1. Proof. exact: liftso1. Qed.
Lemma liftfso_leso S (P Q: 'SO[H]_S) : P ⊑ Q = (liftfso P ⊑ liftfso Q).
Proof. exact: liftso_leso. Qed.
Lemma liftfso_inj S : injective (@liftfso S). Proof. exact: liftso_inj. Qed.
Lemma liftfso_ge0 S (P: 'SO[H]_S) : (0 : 'SO) ⊑ P = ((0 : 'SO) ⊑ liftfso P).
Proof. exact: liftso_ge0. Qed.
Lemma liftfso_le1 S (P: 'SO[H]_S) : P ⊑ :1 = (liftfso P ⊑ :1).
Proof. exact: liftso_le1. Qed.
Lemma liftfso_dual S (P: 'SO[H]_S) : (liftfso P)^*o = liftfso P^*o.
Proof. exact: liftso_dual. Qed.
Lemma liftfso_comp S (P Q: 'SO[H]_S) :liftfso (P :o Q) = liftfso P :o liftfso Q.
Proof. exact: liftso_comp. Qed.
Lemma liftfso_compr S (P Q: 'SO[H]_S) : liftfso (P o: Q) = liftfso P o: liftfso Q.
Proof. exact: liftso_compr. Qed.

Lemma liftfso2 S T (sub : S :<=: T) (f : 'SO[H]_S) :
  liftfso (liftso sub f) = liftfso f.
Proof. by rewrite /liftfso liftso2 subsetTE. Qed.
Lemma liftfsoid S (f : 'SO[H]_S) : liftfso (liftfso f) = liftfso f.
Proof. exact: liftfso2. Qed.

Lemma liftfso_compC S T (f : 'SO[H]_S) (g : 'SO[H]_T) :
  [disjoint S & T] -> liftfso f :o liftfso g = liftfso g :o liftfso f.
Proof. exact: liftso_compC. Qed.

Lemma liftf_fun2 S T (sub : S :<=: T) (F : finType) (f : F -> 'F[H]_S) :
  liftf_fun (lift_fun sub f) = liftf_fun f.
Proof. by rewrite /liftf_fun lift_fun2 subsetTE. Qed.

Lemma liftf_lf_id (f : 'F[H]_setT) : liftf_lf f = f. Proof. exact: lift_lf_id. Qed.
Lemma liftfso_id (E : 'SO[H]_setT) : liftfso E = E. Proof. exact: liftso_id. Qed.
Lemma liftf_fun_id (F : finType) (f : F -> 'F[H]_setT) : liftf_fun f = f.
Proof. exact: lift_fun_id. Qed.

Lemma liftfso_elemso S (F : finType) (M : F -> 'F[H]_S) i :
  liftfso (elemso M i) = elemso (liftf_fun M) i.
Proof. exact: liftso_elemso. Qed.
Lemma liftfso_ifso S (F : finType) (M : F -> 'F[H]_S) (br : F -> 'SO[H]_S) :
  liftfso (ifso M br) = ifso (liftf_fun M) (fun i => liftfso (br i)).
Proof. exact: liftso_ifso. Qed.
Lemma liftfso_whileso S (M : 'TN[H]_(bool;S)) b (D : 'QO[H]_S) :
  liftfso (whileso M b D) = whileso (liftf_fun M) b (liftfso D).
Proof. exact: liftso_whileso. Qed.

Lemma liftf_lf_cast S T (eqST : S = T) (f : 'F[H]_S) :
  liftf_lf (castlf (eqST,eqST) f) = liftf_lf f.
Proof. by case: T / eqST; rewrite castlf_id. Qed.

Lemma liftfso_cast S T (eqST : S = T) (f: 'SO[H]_S) : 
  liftfso (castso (eqST,eqST) f) = liftfso f.
Proof. by case: T / eqST; rewrite castso_id. Qed.

Lemma liftf_lf_compT S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  liftf_lf f \o liftf_lf g = liftf_lf (f \⊗ g).
Proof.
move=>dis; rewrite -(liftf_lf_tenf1r _ dis) -(liftf_lf_tenf1l _ dis).
by rewrite -liftf_lf_comp -tenf_comp ?comp_lfun1l ?comp_lfun1r.
Qed.

Lemma liftfsoEf_compl S T (f : 'F[H]_S) (E : 'SO_T) g :
  [disjoint S & T] ->
  liftfso E (liftf_lf f \o g) = liftf_lf f \o liftfso E g.
Proof.
move=>dis; have ls : S :<=: ~: T by rewrite -disjoints_subset.
rewrite -(liftfso2 (subsetT _)) [liftso _ E]liftfsoE liftfso_cast -{1}(liftf_lf2 ls).
set g' := (castlf (esym(setUCr T),esym(setUCr T)) g).
have Hg: g = liftf_lf g' by rewrite liftf_lf_cast liftf_lf_id.
rewrite Hg [g'](onb_lfun2id deltav_onbasis) pair_big/= !linear_sum/= 
  !linear_sumr/= linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/= -!comp_lfunZr linearZ/=; f_equal.
move: (disjointXC T)=>lt.
rewrite !deltavt -!tenf_outp -!liftf_lf_compT// [in LHS]liftf_lf_compC// 
  comp_lfunA -liftf_lf_comp [in LHS]liftf_lf_compC ?disjointCX//
   !liftf_lf_compT// !liftfsoEf -!tenso_correct// !soE -!liftf_lf_compT// 
   liftf_lf_comp !comp_lfunA; f_equal.
by rewrite liftf_lf2 liftf_lf_compC// disjoint_sym.
Qed.

Lemma liftfsoEf_compr S T (f : 'F[H]_S) (E : 'SO_T) g :
  [disjoint S & T] ->
  liftfso E (g \o liftf_lf f) = liftfso E g \o liftf_lf f.
Proof.
move=>dis; have ls : S :<=: ~: T by rewrite -disjoints_subset.
rewrite -(liftfso2 (subsetT _)) [liftso _ E]liftfsoE liftfso_cast -{1}(liftf_lf2 ls).
set g' := (castlf (esym(setUCr T),esym(setUCr T)) g).
have Hg: g = liftf_lf g' by rewrite liftf_lf_cast liftf_lf_id.
rewrite Hg [g'](onb_lfun2id deltav_onbasis) pair_big/= !linear_sum/= 
  !linear_suml/= linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/= -!comp_lfunZl linearZ/=; f_equal.
move: (disjointXC T)=>lt.
by rewrite !deltavt -!tenf_outp -!liftf_lf_compT// -comp_lfunA -liftf_lf_comp
   !liftf_lf_compT// !liftfsoEf -!tenso_correct// !soE -!liftf_lf_compT// 
   liftf_lf_comp comp_lfunA liftf_lf2.
Qed.
End LiftFullSpace.


