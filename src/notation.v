
From mathcomp Require Import all_ssreflect all_algebra.

(*****************************************************************************)
(*                      Reserved Notations for CoqQ                          *)
(*****************************************************************************)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Reserved Notation "\Tr f" (at level 10, f at level 8).
Reserved Notation "P '^⟂'" (at level 8, format "P ^⟂").
Reserved Notation "f :⊗ g" (at level 45, left associativity).
Reserved Notation "'\Tr_' ( T ) f " (at level 10, f at level 8, format "'\Tr_' ( T )  f").
Reserved Notation "\Rank A" (at level 10, A at level 8, format "\Rank  A").
Reserved Notation "[< u ; v >]" (at level 2, format "[<  u ;  v  >]").
Reserved Notation "[> u ; v <]" (at level 2, format "[>  u ;  v  <]").
Reserved Notation "v ^*v" (at level 8).

Reserved Notation "f ^A" (at level 8, format "f ^A").
Reserved Notation "M ^*m" (at level 8, format "M ^*m").
Reserved Notation "M ^*t" (at level 8, format "M ^*t").
(* Reserved Notation "`<| u |>" (at level 2). *)
Reserved Notation "A :<=: B" (at level 70, no associativity).

Reserved Notation "f ⊗v g" (at level 45, left associativity).
Reserved Notation "f ⊗vm g" (at level 45, left associativity).
Reserved Notation "f \⊗ g" (at level 45, left associativity).
Reserved Notation "f \· g" (at level 40, left associativity).
Reserved Notation "f \O g" (at level 40, left associativity).
Reserved Notation "u '⊗t' v" (at level 45, left associativity).
Reserved Notation "f '⊗f' g" (at level 45, left associativity).
Reserved Notation "A '`⊗`' B" (at level 45, left associativity).

Fact vorder_display : unit. Proof. by []. Qed.
Notation "x '⊑' y" := (@Order.le ring_display _ x y) 
  (at level 70, y at next level, only parsing).
Notation "x '⊏' y" := (@Order.lt ring_display _ x y) 
  (at level 70, y at next level, only parsing).
Notation "x '⊑' y '⊑' z" := ((x ⊑ y) && (y ⊑ z)) 
  (at level 70, y at next level, only parsing).
Notation "'ubounded_by' b f" := (forall i, f i ⊑ b) (at level 10, b, f at next level).
Notation "'lbounded_by' b f" := (forall i, b ⊑ f i) (at level 10, b, f at next level).
Notation "'nondecreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n >= m)%O})
  (at level 10).
Notation "'increasing_seq' f" := ({mono f : n m / (n <= m)%nat >-> (n <= m)%O})
  (at level 10).
Notation "'decreasing_seq' f" := ({mono f : n m / (n <= m)%nat >-> (n >= m)%O})
  (at level 10).

Reserved Notation "''FN'".
Reserved Notation "''FN_' S"       (at level 8, S at level 2, format "''FN_' S").
Reserved Notation "''FN_' ( S )"   (at level 8).
Reserved Notation "''FN[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FN[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FN' ( S )"    (at level 8, format "''FN' ( S )").
Reserved Notation "[ 'normal' 'of' f 'as' g ]" (at level 0, format "[ 'normal'  'of'  f  'as'  g ]").
Reserved Notation "[ 'normal' 'of' f ]"  (at level 0, format "[ 'normal'  'of'  f ]").

Reserved Notation "''FH'".
Reserved Notation "''FH_' S"       (at level 8, S at level 2, format "''FH_' S").
Reserved Notation "''FH_' ( S )"   (at level 8).
Reserved Notation "''FH[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FH[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FH' ( S )"    (at level 8, format "''FH' ( S )").
Reserved Notation "[ 'herm' 'of' f 'as' g ]" (at level 0, format "[ 'herm'  'of'  f  'as'  g ]").
Reserved Notation "[ 'herm' 'of' f ]"  (at level 0, format "[ 'herm'  'of'  f ]").

Reserved Notation "''F+'".
Reserved Notation "''F+_' S"       (at level 8, S at level 2, format "''F+_' S").
Reserved Notation "''F+_' ( S )"   (at level 8).
Reserved Notation "''F+[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''F+[' H ]_ ( S )"     (at level 8).
Reserved Notation "''F+' ( S )"    (at level 8, format "''F+' ( S )").
Reserved Notation "[ 'psd' 'of' f 'as' g ]" (at level 0, format "[ 'psd'  'of'  f  'as'  g ]").
Reserved Notation "[ 'psd' 'of' f ]"  (at level 0, format "[ 'psd'  'of'  f ]").

Reserved Notation "''FO'".
Reserved Notation "''FO_' S"       (at level 8, S at level 2, format "''FO_' S").
Reserved Notation "''FO_' ( S )"   (at level 8).
Reserved Notation "''FO[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FO[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FO' ( S )"    (at level 8, format "''FO' ( S )").
Reserved Notation "[ 'obs' 'of' f 'as' g ]" (at level 0, format "[ 'obs'  'of'  f  'as'  g ]").
Reserved Notation "[ 'obs' 'of' f ]"  (at level 0, format "[ 'obs'  'of'  f ]").

Reserved Notation "''FD'".
Reserved Notation "''FD_' S"       (at level 8, S at level 2, format "''FD_' S").
Reserved Notation "''FD_' ( S )"   (at level 8).
Reserved Notation "''FD[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FD[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FD' ( S )"    (at level 8, format "''FD' ( S )").
Reserved Notation "[ 'den' 'of' f 'as' g ]" (at level 0, format "[ 'den'  'of'  f  'as'  g ]").
Reserved Notation "[ 'den' 'of' f ]"  (at level 0, format "[ 'den'  'of'  f ]").

Reserved Notation "''FD1'".
Reserved Notation "''FD1_' S"       (at level 8, S at level 2, format "''FD1_' S").
Reserved Notation "''FD1_' ( S )"   (at level 8).
Reserved Notation "''FD1[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FD1[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FD1' ( S )"    (at level 8, format "''FD1' ( S )").
Reserved Notation "[ 'den1' 'of' f 'as' g ]" (at level 0, format "[ 'den1'  'of'  f  'as'  g ]").
Reserved Notation "[ 'den1' 'of' f ]"  (at level 0, format "[ 'den1'  'of'  f ]").

Reserved Notation "''FP'".
Reserved Notation "''FP_' S"       (at level 8, S at level 2, format "''FP_' S").
Reserved Notation "''FP_' ( S )"   (at level 8).
Reserved Notation "''FP[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FP[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FP' ( S )"    (at level 8, format "''FP' ( S )").
Reserved Notation "[ 'proj' 'of' f 'as' g ]" (at level 0, format "[ 'proj'  'of'  f  'as'  g ]").
Reserved Notation "[ 'proj' 'of' f ]"  (at level 0, format "[ 'proj'  'of'  f ]").

Reserved Notation "''FP1'".
Reserved Notation "''FP1_' S"       (at level 8, S at level 2, format "''FP1_' S").
Reserved Notation "''FP1_' ( S )"   (at level 8).
Reserved Notation "''FP1[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FP1[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FP1' ( S )"    (at level 8, format "''FP1' ( S )").
Reserved Notation "[ 'proj1' 'of' f 'as' g ]" (at level 0, format "[ 'proj1'  'of'  f  'as'  g ]").
Reserved Notation "[ 'proj1' 'of' f ]"  (at level 0, format "[ 'proj1'  'of'  f ]").

Reserved Notation "''FI'" .
Reserved Notation "''FI_' S"     (at level 8, S at level 2, format "''FI_' S").
Reserved Notation "''FI_' ( S )" (at level 8).
Reserved Notation "''FI_' ( S , T )" (at level 8, format "''FI_' ( S ,  T )").
Reserved Notation "''FI[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''FI[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FI[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''FI' ( S )"  (at level 8, format "''FI' ( S )").
Reserved Notation "''FI' ( S , T )"  (at level 8, format "''FI' ( S ,  T )").

Reserved Notation "''FU'".
Reserved Notation "''FU_' S"       (at level 8, S at level 2, format "''FU_' S").
Reserved Notation "''FU_' ( S )"   (at level 8).
Reserved Notation "''FU[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''FU[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FU' ( S )"    (at level 8, format "''FU' ( S )").
Reserved Notation "[ 'unitary' 'of' f 'as' g ]" (at level 0, format "[ 'unitary'  'of'  f  'as'  g ]").
Reserved Notation "[ 'unitary' 'of' f ]"  (at level 0, format "[ 'unitary'  'of'  f ]").

Reserved Notation "''SO'" .
Reserved Notation "''SO_' S"     (at level 8, S at level 2, format "''SO_' S").
Reserved Notation "''SO_' ( S )" (at level 8).
Reserved Notation "''SO_' ( S , T )" (at level 8, format "''SO_' ( S ,  T )").
Reserved Notation "''SO[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''SO[' H ]_ ( S )"     (at level 8).
Reserved Notation "''SO[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''SO' ( S )"  (at level 8, format "''SO' ( S )").
Reserved Notation "''SO' ( S , T )"  (at level 8, format "''SO' ( S ,  T )").

Reserved Notation ":1".
Reserved Notation "\:1".
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

Reserved Notation "''PS'".
Reserved Notation "''PS_' S"       (at level 8, S at level 2, format "''PS_' S").
Reserved Notation "''PS_' ( S )"   (at level 8).
Reserved Notation "''PS[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''PS[' H ]_ ( S )"     (at level 8).
Reserved Notation "''PS' ( S )"    (at level 8, format "''PS' ( S )").
Reserved Notation "[ 'PS' 'of' f 'as' g ]" (at level 0, format "[ 'PS'  'of'  f  'as'  g ]").
Reserved Notation "[ 'PS' 'of' f ]"  (at level 0, format "[ 'PS'  'of'  f ]").

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


(* for cqwhile *)
Declare Custom Entry reg.

Reserved Notation "''D'" (at level 8, format "''D'").
Reserved Notation "''D[' H ]" (at level 8). (* only parsing *)
Reserved Notation "''D_' S"     (at level 8, S at level 2, format "''D_' S").
Reserved Notation "''D_' ( S )" (at level 8). (* only parsing *)
Reserved Notation "''D_' ( S , T )" (at level 8, format "''D_' ( S ,  T )").
Reserved Notation "''D[' H ]_ S"    (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''D[' H ]_ ( S )"     (at level 8). (* only parsing *)
Reserved Notation "''D[' H ]_ ( S , T )" (at level 8). (* only parsing *)
Reserved Notation "''Ket_' S"     (at level 8, S at level 2, format "''Ket_' S").
Reserved Notation "''Ket_' ( S )" (at level 8). (* only parsing *)
Reserved Notation "''Ket[' H ]_ S"    (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''Ket[' H ]_ ( S )"     (at level 8). (* only parsing *)
Reserved Notation "''Bra_' S"     (at level 8, S at level 2, format "''Bra_' S").
Reserved Notation "''Bra_' ( S )" (at level 8). (* only parsing *)
Reserved Notation "''Bra[' H ]_ S"    (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''Bra[' H ]_ ( S )"     (at level 8). (* only parsing *)

Reserved Notation "'\1_' S" (at level 10, S at next level, format "\1_ S").
(* Reserved Notation " '\tr_(' q ) e " (at level 10, q at next level).  *)
Reserved Notation "c %:D" (at level 2, left associativity, format "c %:D").
Reserved Notation " 'o%D' " (at level 0).
Reserved Notation " '⊗%D' " (at level 0).
Reserved Notation " '·%D' " (at level 0).

Reserved Notation "\dirac_ ( i , j ) E" (at level 36, E at level 36, i, j at level 50,
  format "\dirac_ ( i ,  j )  E").
Reserved Notation " e '.dom'" (at level 2).
Reserved Notation " e '.cdom'" (at level 2).
Reserved Notation "''|' x >" (at level 2, x at level 60, format "''|' x >").
Reserved Notation "''<' x |" (at level 2, x at level 60, format "''<' x |").
Reserved Notation "''|' x >< y |" (at level 2, x at level 60, y at next level, format "''|' x >< y |").
Reserved Notation "''<' x | y >" (at level 2, x at level 60, y at next level, format "''<' x | y >").
Reserved Notation "''[' x ]" (at level 2, x at level 60, format "''[' x ]").

Reserved Notation "''|' x ; y >" (at level 2, x at level 60, y custom reg, format "''|' x ; y >").
Reserved Notation "''<' x ; y |" (at level 2, x at level 60, y custom reg, format "''<' x ; y |").
Reserved Notation "''|' x >< z ; w |" (at level 2, x at level 60, z at next level, w custom reg, format "''|' x >< z ; w |").
Reserved Notation "''|' x ; y >< z ; w |" (at level 2, x at level 60, z at next level, y custom reg, w custom reg, format "''|' x ; y >< z ; w |").
Reserved Notation "''<' x | z ; w >" (at level 2, x at level 60, z at next level, w custom reg, format "''<' x | z ; w >").
Reserved Notation "''<' x ; y | z ; w >" (at level 2, x at level 60, z at next level, y custom reg, w custom reg, format "''<' x ; y | z ; w >").
Reserved Notation "''[' x ; y ]" (at level 2, x at level 60, y custom reg, format "''[' x ; y ]").

Reserved Notation "''|' x , y >" (at level 2, x, y at level 60, format "''|' x ,  y >").
(* Reserved Notation "''|' x , ( y ) >" (at level 2, x at level 60, y at next level). (* only parsing *) *)
Reserved Notation "''|' x , y ; z >" (at level 2, x, y at level 60, z at next level, format "''|' x ,  y ; z >").
Reserved Notation "''<' x , y |" (at level 2, x, y at level 60, format "''<' x ,  y |").
(* Reserved Notation "''<' x , ( y ) |" (at level 2, x at level 60, y at next level). (* only parsing *) *)
Reserved Notation "''<' x , y ; z |" (at level 2, x, y at level 60, z at next level, format "''<' x ,  y ; z |").
Reserved Notation "''|' x >< z , w |" (at level 2, x at level 60, z, w at next level, format "''|' x >< z ,  w |").
(* Reserved Notation "''|' x >< z , ( w ) |" (at level 2, x at level 60, z,w at next level).  (* only parsing *) *)
Reserved Notation "''|' x >< z , w ; t |" (at level 2, x at level 60, z, w, t at next level, format "''|' x >< z ,  w ; t |").
Reserved Notation "''[' x , y ]" (at level 2, x at level 60, format "''[' x ,  y ]").
(* Reserved Notation "''[' x , ( y ) ]" (at level 2, x at level 60, y at next level). (* only parsing *) *)
Reserved Notation "''[' x , y ; z ]" (at level 2, x at level 60, z at next level, format "''[' x ,  y ; z ]").

(*
Section test.
Require Import forms.
Open Scope ring_scope.
Variable (R : ringType).
Notation "( x )" := x (in custom reg at level 0).
Notation "x" := x (in custom reg at level 0, x constr at level 0).
Notation "x %:R" := (x%:R : R).

Notation "''|' x >" := (x%:R).
Notation "''<' x |" := (-x%:R).
Notation "''|' x >< y |" := (x%:R - y%:R).
Notation "''<' x | y >" := (- x%:R + y%:R).
Notation "''[' x ]" := (x%:R * x%:R).

Notation "''|' x ; y >" := (x%:R * y%:R).
Notation "''<' x ; y |" := (- x%:R * y%:R).
Notation "''|' x >< z ; w |" := (x%:R - z%:R * w%:R).
Notation "''|' x ; y >< z ; w |" := (x%:R * y%:R - z%:R * w%:R).
Notation "''<' x | z ; w >" := (- x%:R + z%:R * w%:R).
Notation "''<' x ; y | z ; w >" := (- x%:R * y%:R + z%:R * w%:R).
Notation "''[' x ; y ]" := (x%:R * x%:R * y%:R * y%:R).

Notation "''|' x , y >" := (x%:R * y%:R).
 (* (at level 2, x, y at level 60, format "''|' x ,  y >"). *)
(* Notation "''|' x , ( y ) >" (at level 2, x at level 60, y at next level). (* only parsing *) *)
Notation "''|' x , y ; z >" := (x%:R * (y%:R + z%:R)).
 (* (at level 2, x, y at level 60, z at next level, format "''|' x ,  y ; z >"). *)
Notation "''<' x , y |" := (- x%:R * y%:R).
 (* (at level 2, x at level 60, format "''<' x ,  y |"). *)
(* Notation "''<' x , ( y ) |" (at level 2, x at level 60, y at next level). (* only parsing *) *)
Notation "''<' x , y ; z |" := (- x%:R * (y%:R + z%:R)).
 (* (at level 2, x at level 60, z at next level, format "''<' x ,  y ; z |"). *)
Notation "''|' x >< z , w |" := (x%:R - z%:R * w%:R).
 (* (at level 2, x at level 60, z,w at next level, format "''|' x >< z ,  w |"). *)
(* Notation "''|' x >< z , ( w ) |" (at level 2, x at level 60, z,w at next level).  (* only parsing *) *)
Notation "''|' x >< z , w ; t |" := (x%:R - z%:R * (w%:R + t%:R)).
 (* (at level 2, x at level 60, z,w,t at next level, format "''|' x >< z ,  w ; t |"). *)
Notation "''[' x , y ]" := (x%:R * x%:R * y%:R * y%:R).
 (* (at level 2, x at level 60, format "''[' x ,  y ]"). *)
(* Notation "''[' x , ( y ) ]" (at level 2, x at level 60, y at next level). (* only parsing *) *)
Notation "''[' x , y ; z ]" := (x%:R * x%:R * (y%:R * y%:R - z%:R * z%:R)).
 (* (at level 2, x at level 60, z at next level, format "''[' x ,  y ; z ]"). *)

Local Open Scope nat_scope.

Check '|1>.
Check '<1|.
Check '|1><2|.
Check '<1|2>.
Check '[1].
Check '|1; 2 >.
Check '<1 ; 2|.
Check '|1 >< 2; 3|.
Check '|1;2><3;4|.
Check '<1|2;3>.
Check '<1;2|3;4>.
Check '[1;2].

Check '|1,(2>1)>.
Check '|1,2;3>.

Check '|1,2>.
Check '|1,(2)>.
Check '|1,2;3>.
Check '<1,2|.
Check '<1,2;3|.
Check '|1><2,3|.
Check '|1><2,3;4|.
Check '[1,2].
Check '[1,2;(3+4)].

End test.
*)

(* deprecated for cqwhile *)
(* Reserved Notation "'| v >" (at level 10, v at level 99, no associativity). *)
(* Reserved Notation "'| v ; x >" (at level 10, v at level 99, x at next level, no associativity).
Reserved Notation "'| v ; x , y >" (at level 10, v at level 99, x, y at next level, no associativity).
(* Reserved Notation "'< v |" (at level 10, v at level 99, no associativity). *)
Reserved Notation "'< v ; x |" (at level 10, v at level 99, x at next level, no associativity).
Reserved Notation "'< v ; x , y |" (at level 10, v at level 99, x,y at next level, no associativity).
Reserved Notation "'[ M ]" (at level 10, M at level 99, no associativity).
Reserved Notation "'[ M ; x ]" (at level 10, M at level 99, x at next level, no associativity).
Reserved Notation "'[ M ; x , y ]" (at level 10, M at level 99, x,y at next level, no associativity).
Reserved Notation "'| v > x '< u |" (at level 10, v,u at level 99, x at next level, no associativity).
Reserved Notation "'| v > ( x , y ) '< u |" (at level 10, v,u at level 99, x,y at next level, no associativity). *)

Reserved Notation "\mul_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \mul_ i '/  '  F ']'").
Reserved Notation "\mul_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \mul_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\mul_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \mul_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\mul_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \mul_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\mul_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \mul_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\mul_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \mul_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\mul_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\mul_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\mul_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \mul_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\mul_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \mul_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\mul_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \mul_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\mul_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \mul_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\ten_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \ten_ i '/  '  F ']'").
Reserved Notation "\ten_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \ten_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\ten_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \ten_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\ten_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \ten_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\ten_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \ten_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\ten_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \ten_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\ten_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\ten_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\ten_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \ten_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\ten_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \ten_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\ten_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \ten_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\ten_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \ten_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\dot_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \dot_ i '/  '  F ']'").
Reserved Notation "\dot_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \dot_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \dot_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\dot_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \dot_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \dot_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\dot_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \dot_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\dot_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\dot_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \dot_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \dot_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\dot_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \dot_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\dot_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \dot_ ( i  'in'  A ) '/  '  F ']'").