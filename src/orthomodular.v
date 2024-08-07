(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.

(****************************************************************************)
(*                     Module for orthomodular lattice                      *)
(* ------------------------------------------------------------------------ *)
(* We provide the following interfaces for lattice theory:                  *)
(*                                                                          *)
(*        complLatticeType d == the type of complement lattice              *)
(*                              The HB class is called ComplLattice.        *)
(*                                                                          *)
(*        orthoLatticeType d == the type of orthogonal lattice              *)
(*                              The HB class is called OrthoLattice.        *)
(*                                                                          *)
(*     oModularLatticeType d == the type of orthomodular lattice            *)
(*                              The HB class is called OModularLattice.     *)
(*                                                                          *)
(*      modularLatticeType d == the type of modular lattice                 *)
(*                              The HB class is called ModularLattice.      *)
(* ------------------------------------------------------------------------ *)
(* * Operations :                                                           *)
(*                    ~` A : ocompl (suffix 'O')                            *)
(*                  ~`^d A : dual_ocompl                                    *)
(*                 x _|_ y : orthogonal                                     *)
(*                 x _C_ y : commute                                        *)
(*                 x _D_ y : dual_commute                                   *)
(*                 x _M_ y : ortho_commute                                  *)
(*                x `=>` y : sasaki_hook (suffix 'H')                       *)
(*                x `&&` y : sasaki_projection (suffix 'J')                 *)
(* ------------------------------------------------------------------------ *)
(* * Theories :                                                             *)
(* We establish foundational theories of orthomodular lattices following    *)
(* from [Beran 1985; Gabriëls et al . 2017], prove extensive properties     *)
(* and tactics for determining the equivalence and order relations of       *)
(* free bivariate formulas [Beran 1985].                                    *)
(*                                                                          *)
(* Use tactic "OM_autodec a b" to automatically solve any equivalence or    *)
(* order relation between two variables.                                    *)
(****************************************************************************)

Import Order Order.LTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* note that the complement here is different from that in order *)

(* complement top bottom lattice *)

HB.mixin Record has_ocompl (d : unit) T of TBLattice d T := {
  ocompl : T -> T;
  joinOx : forall a, join (ocompl a) a = top;
  meetOx : forall a, meet (ocompl a) a = bottom;
}.

#[short(type="complLatticeType")]
HB.structure Definition ComplLattice (d : unit) :=
  { T of TBLattice d T & has_ocompl d T }.

Module ComplLatticeExports.
#[deprecated(since="mathcomp 2.0.0", note="Use ComplLattice.clone instead.")]
Notation "[ 'complLatticeType' 'of' T 'for' cT ]" :=
  (ComplLattice.clone _ T%type cT)
  (at level 0, format "[ 'complLatticeType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ComplLattice.clone instead.")]
Notation "[ 'complLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (ComplLattice.clone disp T%type cT)
  (at level 0, format "[ 'complLatticeType'  'of'  T  'for'  cT  'with'  disp ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ComplLattice.clone instead.")]
Notation "[ 'complLatticeType' 'of' T ]" := (ComplLattice.clone _ T%type _)
  (at level 0, format "[ 'complLatticeType'  'of'  T ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ComplLattice.clone instead.")]
Notation "[ 'complLatticeType' 'of' T 'with' disp ]" :=
  (ComplLattice.clone disp T%type _)
  (at level 0, format "[ 'complLatticeType'  'of'  T  'with' disp ]") : form_scope.
End ComplLatticeExports.
HB.export ComplLatticeExports.

Module Import ComplLatticeSyntax.
Notation "~` A" := (ocompl A) : order_scope.
Notation dual_ocompl := (@ocompl (dual_display _) _).
Notation "~`^d A" := (dual_ocompl A)
  (at level 35, right associativity) : order_scope.
End ComplLatticeSyntax.

(* orthocomplement lattice *)
HB.mixin Record ComplLattice_isOrthoLattice (d : unit) T of ComplLattice d T := {
  ocomplK : involutive (@ocompl _ T);
  leOP : {homo (@ocompl _ T) : a b /~ a <= b};
}.

#[short(type="orthoLatticeType")]
HB.structure Definition OrthoLattice (d : unit):=
  { T of ComplLattice d T & ComplLattice_isOrthoLattice d T }.

Module OrthoLatticeExports.
#[deprecated(since="mathcomp 2.0.0", note="Use OrthoLattice.clone instead.")]
Notation "[ 'orthoLatticeType' 'of' T 'for' cT ]" :=
  (OrthoLattice.clone _ T%type cT)
  (at level 0, format "[ 'orthoLatticeType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use OrthoLattice.clone instead.")]
Notation "[ 'orthoLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (OrthoLattice.clone disp T%type cT)
  (at level 0, format "[ 'orthoLatticeType'  'of'  T  'for'  cT  'with'  disp ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use OrthoLattice.clone instead.")]
Notation "[ 'orthoLatticeType' 'of' T ]" := (OrthoLattice.clone _ T%type _)
  (at level 0, format "[ 'orthoLatticeType'  'of'  T ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use OrthoLattice.clone instead.")]
Notation "[ 'orthoLatticeType' 'of' T 'with' disp ]" :=
  (OrthoLattice.clone disp T%type _)
  (at level 0, format "[ 'orthoLatticeType'  'of'  T  'with' disp ]") : form_scope.
End OrthoLatticeExports.
HB.export OrthoLatticeExports.

Reserved Notation "x '_|_' y" (at level 69, format "x  _|_  y").
Reserved Notation "x '_C_' y" (at level 69, format "x  _C_  y").
Reserved Notation "x '_D_' y" (at level 69, format "x  _D_  y").
Reserved Notation "x '_M_' y" (at level 69, format "x  _M_  y").
Definition orthogonal (disp : unit) (T : orthoLatticeType disp) : rel T := 
    fun (x y : T) => (x <= ~` y).
Definition commute (disp : unit) (T : orthoLatticeType disp) : rel T := 
    fun (x y : T) => (x == ((x `&` y) `|` (x `&` ~` y))).
Definition dual_commute (disp : unit) (T : orthoLatticeType disp) : rel T := 
    fun (x y : T) => (x == ((x `|` y) `&` (x `|` ~` y))).
Definition sasaki_hook (disp : unit) (T : orthoLatticeType disp) (x y : T) : T := 
  ~` x `|` (x `&` y).
Definition sasaki_projection (disp : unit) (T : orthoLatticeType disp) (x y : T) : T := 
  x `&` (~` x `|` y).
(* we here give the alternative definition of orthogonally commutes *)
(* x _M_ y iff exists x1 y1 z s.t.  x = x1 `|` z, y = y1 `|` z, x1 _|_ z *)
(*   y1 _|_ z, x1 _|_ y1 . two definition are indeed equivalent *)
Definition ortho_commute (disp : unit) (T : orthoLatticeType disp) : rel T := 
  fun (x y : T) => commute x y && commute y x.
Notation "x '_|_' y" := (orthogonal x y) : order_scope.
Notation "x '_C_' y" := (commute x y) : order_scope.
Notation "x '_D_' y" := (dual_commute x y) : order_scope.
Notation "x '_M_' y" := (ortho_commute x y) : order_scope.
Notation "x '`=>`' y" := (sasaki_hook x y) (at level 70) : order_scope.
Notation "x '`&&`' y" := (sasaki_projection x y) (at level 70) : order_scope.

(* orthomodular lattice *)
Definition orthomodular_law (d : unit) (T : orthoLatticeType d) :=
  forall a b : T, a <= b -> a `|` ((~` a) `&` b) = b.
HB.mixin Record hasOrthoModular (d : unit) T of OrthoLattice d T := {
  le_joinIO : forall a b : T, a <= b -> join a (meet (ocompl a) b) = b;
}.

#[short(type="oModularLatticeType")]
HB.structure Definition OModularLattice (d : unit):=
  { T of OrthoLattice d T & hasOrthoModular d T }.

Module OModularLatticeExports.
#[deprecated(since="mathcomp 2.0.0", note="Use OModularLattice.clone instead.")]
Notation "[ 'oModularLatticeType' 'of' T 'for' cT ]" := (OModularLattice.clone _ T%type cT)
  (at level 0, format "[ 'oModularLatticeType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use OModularLattice.clone instead.")]
Notation "[ 'oModularLatticeType' 'of' T 'for' cT 'with' disp ]" := (OModularLattice.clone disp T%type cT)
  (at level 0, format "[ 'oModularLatticeType'  'of'  T  'for'  cT  'with'  disp ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use OModularLattice.clone instead.")]
Notation "[ 'oModularLatticeType' 'of' T ]" := (OModularLattice.clone _ T%type _)
  (at level 0, format "[ 'oModularLatticeType'  'of'  T ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use OModularLattice.clone instead.")]
Notation "[ 'oModularLatticeType' 'of' T 'with' disp ]" := (OModularLattice.clone disp T%type _)
  (at level 0, format "[ 'oModularLatticeType'  'of'  T  'with' disp ]") : form_scope.
End OModularLatticeExports.
HB.export OModularLatticeExports.

(* modular lattice *)
Definition modular_law (d : unit) (T : orthoLatticeType d) :=
  forall a b c : T, a <= c -> a `|` (b `&` c) = (a `|` b) `&` c.
HB.mixin Record hasModular (d : unit) T of OModularLattice d T := {
  le_joinI : forall a b c : T,
    a <= c -> join a (meet b c) = meet (join a b) c;
}.

#[short(type="modularLatticeType")]
HB.structure Definition ModularLattice (d : unit):=
  { T of OModularLattice d T & hasModular d T }.

Module ModularLatticeExports.
#[deprecated(since="mathcomp 2.0.0", note="Use ModularLattice.clone instead.")]
Notation "[ 'modularLatticeType' 'of' T 'for' cT ]" := (ModularLattice.clone _ T%type cT)
  (at level 0, format "[ 'modularLatticeType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ModularLattice.clone instead.")]
Notation "[ 'modularLatticeType' 'of' T 'for' cT 'with' disp ]" := (ModularLattice.clone disp T%type cT)
  (at level 0, format "[ 'modularLatticeType'  'of'  T  'for'  cT  'with'  disp ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ModularLattice.clone instead.")]
Notation "[ 'modularLatticeType' 'of' T ]" := (ModularLattice.clone _ T%type _)
  (at level 0, format "[ 'modularLatticeType'  'of'  T ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ModularLattice.clone instead.")]
Notation "[ 'modularLatticeType' 'of' T 'with' disp ]" := (ModularLattice.clone disp T%type _)
  (at level 0, format "[ 'modularLatticeType'  'of'  T  'with' disp ]") : form_scope.
End ModularLatticeExports.
HB.export ModularLatticeExports.

Section LatticeExtra.
Variable (disp : unit) (T : latticeType disp).
Implicit Type (x y z : T).

Lemma le_joinl z : {homo (join z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leU2. Qed.

Lemma le_joinr z : {homo (join^~ z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leU2. Qed.

Lemma lt_joinl z : {homo (join z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leU2=>//; apply ltW. Qed.

Lemma lt_joinr z : {homo (join^~ z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leU2=>//; apply ltW. Qed.

Lemma le_meetl z : {homo (meet z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leI2. Qed.

Lemma le_meetr z : {homo (meet^~ z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leI2. Qed.

Lemma lt_meetl z : {homo (meet z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leI2=>//; apply ltW. Qed.

Lemma lt_meetr z : {homo (meet^~ z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leI2=>//; apply ltW. Qed.

End LatticeExtra.

Section ComplLatticeTheory.
Variable (disp : unit) (T : complLatticeType disp).
Implicit Type (x y : T).

Lemma joinxO x : x `|` ~` x = \top.
Proof. by rewrite joinC joinOx. Qed.
Lemma meetxO x : x `&` ~` x = \bot.
Proof. by rewrite meetC meetOx. Qed.

Lemma ocompl1 : ~` \top = \bot :> T.
Proof. by rewrite -(meetxO \top) meet1x. Qed.

Lemma ocompl0 : ~` \bot = \top :> T.
Proof. by rewrite -(joinOx \bot) joinx0. Qed.

End ComplLatticeTheory.

Module Import DualComplLattice.
Section DualComplLattice.
Context {disp : unit} {L : complLatticeType disp}.
HB.instance Definition _ := has_ocompl.Build (dual_display disp) L^d meetOx joinOx.
End DualComplLattice.
End DualComplLattice.
(* add theories later *)

Section OrthoLatticeTheory.
Variable (disp : unit) (T : orthoLatticeType disp).
Implicit Type (x y : T).

Lemma leO : {mono (@ocompl _ T) : a b /~ a <= b}.
Proof.
move=>a b; apply/Bool.eq_iff_eq_true; split.
rewrite -{2}(ocomplK b) -{2}(ocomplK a).
all: apply leOP.
Qed.

Lemma lexO x y : x <= ~` y = (y <= ~` x).
Proof. by rewrite -leO ocomplK. Qed.

Lemma leOx x y : ~` x <= y = (~` y <= x).
Proof. by rewrite -leO ocomplK. Qed.

Lemma ocompl_inj : injective (@ocompl _ T).
Proof. exact: (can_inj ocomplK). Qed.

Lemma ocomplU x y : ~` (x `|` y) = ~` x `&` ~` y.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
by rewrite lexI !leO ?leUl ?leUr.
by rewrite -leO ocomplK leUx lexO leIl lexO leIr.
Qed.

Lemma ocomplI  x y : ~` (x `&` y) = ~` x `|` ~` y.
Proof. by rewrite -[RHS]ocomplK ocomplU !ocomplK. Qed.

Lemma lexO_disj x y : (x <= ~` y) -> (x `&` y = \bot).
Proof. by move/(le_meetr y); rewrite meetOx lex0=>/eqP. Qed.

Lemma modular_is_orthomodular : modular_law T -> orthomodular_law T.
Proof. by move=>P1 x y /P1 P2; move: (P2 (~` x))=>->; rewrite joinxO meet1x. Qed.

(* orthogonal *)

Lemma ortho_idP x : x _|_ x = (x == \bot).
Proof. by rewrite /orthogonal -leIidl meetxO lex0. Qed.

Lemma orthoC x y : x _|_ y = y _|_ x.
Proof. by rewrite /orthogonal lexO. Qed.

Lemma orthoIl x y z : x _|_ y -> x _|_ (y `&` z).
Proof. rewrite /orthogonal ocomplI; apply: lexUl. Qed.

Lemma orthoIr x y z : x _|_ y -> x _|_ (z `&` y).
Proof. rewrite /orthogonal ocomplI; apply: lexUr. Qed.

Lemma orthoU x y z : (x _|_ y) && (x _|_ z) = x _|_ (y `|` z).
Proof. by rewrite /orthogonal ocomplU lexI. Qed.

(* commute *)
Lemma ortho_commuteC x y : x _M_ y = y _M_ x.
Proof. by rewrite /ortho_commute andbC. Qed.

Lemma ortho_commuteP x y : 
  reflect (exists x1 y1 z,
    x = x1 `|` z /\ y = y1 `|` z /\ x1 _|_ z /\ y1 _|_ z /\ x1 _|_ y1)
          (x _M_ y).
Proof.
apply/(iffP idP).
  rewrite /ortho_commute=>/andP[] P1 P2.
  exists (x `&` ~` y); exists (~` x `&` y); exists (x `&` y); do ! split.
  by move: P1=>/eqP{1}->; rewrite joinC.
  by move: P2=>/eqP{1}->; rewrite meetC joinC meetC.
  by rewrite /orthogonal ocomplI; apply/(le_trans (leIr _ _))/leUr.
  by rewrite /orthogonal ocomplI; apply/(le_trans (leIl _ _))/leUl.
  by rewrite /orthogonal ocomplI ocomplK; apply/(le_trans (leIl _ _))/leUl.
move=>[x1][y1][z][->][->]; rewrite /orthogonal=>[[]P1 []P2 P3].
rewrite /ortho_commute /commute; apply/andP; split.
  apply/eqP/le_anti/andP; split; last by rewrite leUx !leIl.
  by rewrite {1}joinC; apply: leU2;
  rewrite lexI ?leUr// leUl/= ocomplU lexI P1 P3.
apply/eqP/le_anti/andP; split; last by rewrite leUx !leIl.
by rewrite {1}joinC; apply: leU2;
rewrite lexI ?leUr// leUl/= ocomplU lexI P2 lexO P3.
Qed.

Lemma commutexx x : x _C_ x.
Proof. by rewrite /commute meetxx meetxO joinx0. Qed.

Lemma commutexO x y : x _C_ ~` y = x _C_ y.
Proof. by rewrite /commute ocomplK joinC. Qed.

Lemma dual_commutexO x y : x _D_ ~` y = x _D_ y.
Proof. by rewrite /dual_commute ocomplK meetC. Qed.

Lemma commuteOO_dual x y : ~` x _C_ ~` y = x _D_ y. 
Proof.
by rewrite /commute /dual_commute
  -!ocomplU -ocomplI (inj_eq ocompl_inj).
Qed.

Lemma dual_commuteOO x y : ~` x _D_ ~` y = x _C_ y. 
Proof. by rewrite -commuteOO_dual !ocomplK. Qed.

Lemma le_commute x y : x <= y -> x _C_ y.
Proof. by rewrite leEmeet /commute=>/eqP->; rewrite meetKU. Qed.

Lemma le_dual_commute x y : y <= x -> x _D_ y.
Proof. by rewrite -leO=>/le_commute; rewrite -commuteOO_dual. Qed.

Lemma lexO_commute x y : x <= ~` y -> x _C_ y.
Proof. by move=>/le_commute; rewrite commutexO. Qed.

Lemma leOx_dual_commute x y : ~` y <= x -> x _D_ y.
Proof. by move=>/le_dual_commute; rewrite dual_commutexO. Qed.

(* equivalent characterization of orthomodular law *)

Lemma orthomodular_le_meetUO : orthomodular_law T <->
  (forall x y, y <= x -> x `&` (~` x `|` y) = y).
Proof.
by split=>P x y; rewrite -leO=>/P;
rewrite -!(ocomplU,ocomplI)=>/ocompl_inj.
Qed.

Lemma orthomodular_le_meet0_eqO : orthomodular_law T <->
  (forall x y, ~` y <= x -> x `&` y = \bot -> x = ~` y).
Proof.
split=> + x y P1.
by move=>/orthomodular_le_meetUO/(_ _ _ P1)<-;
  rewrite -ocomplI=>->; rewrite ocompl0 meetx1.
move=>/(_ y (~` (x `|` (~` x `&` y)))); rewrite ocomplK=><-//.
by rewrite leUx P1/= leIr.
by rewrite ocomplU meetA [y `&` _]meetC meetxO.
Qed.

Lemma orthomodular_le_join1_eqO : orthomodular_law T <->
  (forall x y, x <= ~`y -> x `|` y = \top -> x = ~` y).
Proof.
rewrite orthomodular_le_meet0_eqO; split=>P x y P1 P2;
by move: (P (~` x) (~` y)); rewrite leO -?ocomplU -?ocomplI 
  P2 ?ocompl1 ?ocompl0=>/(_ P1 erefl)/ocompl_inj.
Qed.

Lemma orthomodular_commuteC : orthomodular_law T <-> 
  (commutative (@commute _ T)).
Proof.
split; last first.
  move=>Pc x y le; move: {+}le=>/le_commute;
  rewrite Pc /commute ![y `&` _]meetC.
  by move: le; rewrite leEmeet=>/eqP->/eqP.
move=>Po a b; apply/Bool.eq_iff_eq_true.
suff P (x y : T) : x _C_ y -> y _C_ x by split=>/P.
rewrite /commute=>/eqP P1; apply/eqP.
rewrite -[RHS]ocomplK ocomplU ocomplI ocomplI ocomplK.
move: {+}Po=>/orthomodular_le_meet0_eqO; apply.
  by rewrite ocomplI !ocomplU !ocomplK leUx !leIl.
rewrite -(meetxO y); f_equal; move: Po.
rewrite orthomodular_le_meetUO=>/(_ (~` x `|` ~` y) (~` y) (leUr _ _)){3}<-.
by rewrite joinC; f_equal; 
  rewrite {1}P1 joinC -joinA [X in _ `|` X]joinC meetKUC ocomplU !ocomplK.
Qed.

Lemma orthomodular_commuteOx : orthomodular_law T <-> 
  (forall x y, ~` x _C_ y = x _C_ y).
Proof.
split.
by rewrite orthomodular_commuteC=>P x y; rewrite P commutexO P.
move=>P x y le; move: {+}le; rewrite -leO=>/le_commute; 
rewrite P /commute ocomplK [y `&` x]meetC.
by move: le; rewrite leEmeet=>/eqP->/eqP; rewrite joinC meetC.
Qed.

Lemma orthomodular_commute_dual_eq : orthomodular_law T <-> 
  (forall x y, x _C_ y = x _D_ y).
Proof.
split; rewrite orthomodular_commuteOx=>P x y.
by rewrite -P -commutexO -dual_commuteOO !ocomplK.
by rewrite -commutexO commuteOO_dual -P.
Qed.

Lemma orthomodular_commute_ortho_eq : orthomodular_law T <-> 
  (forall x y, x _C_ y = x _M_ y).
Proof.
split; rewrite orthomodular_commuteC=>P x y.
by rewrite /ortho_commute P andbb.
by rewrite !P ortho_commuteC.
Qed.

End OrthoLatticeTheory.

Arguments ocompl_inj {disp T}.

Module Import DualOrthoLattice.
Section DualOrthoLattice.
Context {disp : unit} {L : orthoLatticeType disp}.

Lemma dual_leOP : {homo (@ocompl _ L^d) : a b /~ a <= b}.
Proof. by move=>a b; rewrite /ocompl/= /Order.le/= leO. Qed.

HB.instance Definition _ :=
  ComplLattice_isOrthoLattice.Build (dual_display disp) L^d ocomplK dual_leOP.
End DualOrthoLattice.
End DualOrthoLattice.

Section OModularLatticeTheory.
Variable (disp : unit) (T : oModularLatticeType disp).
Implicit Type (x y a b : T).

Lemma le_meetUO x y : y <= x -> x `&` (~` x `|` y) = y.
Proof. by move: x y; rewrite -orthomodular_le_meetUO; exact le_joinIO. Qed.

Lemma le_meet0_eqO x y : ~` y <= x -> x `&` y = \bot -> x = ~` y.
Proof. by move: x y; rewrite -orthomodular_le_meet0_eqO; exact le_joinIO. Qed.

Lemma le_join1_eqO x y : x <= ~`y -> x `|` y = \top -> x = ~` y.
Proof. by move: x y; rewrite -orthomodular_le_join1_eqO; exact le_joinIO. Qed.

Lemma commuteC : (commutative (@commute _ T)).
Proof. by rewrite -orthomodular_commuteC; exact le_joinIO. Qed.

Lemma commuteOx x y : ~` x _C_ y = x _C_ y.
Proof. by move: x y; rewrite -orthomodular_commuteOx; exact le_joinIO. Qed.

Lemma commuteOO x y : ~` x _C_ ~` y = x _C_ y.
Proof. by rewrite commuteOx commutexO. Qed.

Lemma dual_commute_eq x y : x _D_ y = x _C_ y.
Proof.
symmetry; move: x y; rewrite -orthomodular_commute_dual_eq;
exact le_joinIO.
Qed.

Lemma ortho_commute_eq x y : x _M_ y = x _C_ y.
Proof. by rewrite /ortho_commute commuteC andbb. Qed.

Lemma commute_char2 a b : ((a `|` ~` b) `&` b == a `&` b) = a _C_ b.
Proof.
apply/Bool.eq_iff_eq_true; split.
move=>/eqP P; rewrite commuteC /commute meetC -P joinC -[a `|` ~` b]joinC.
by rewrite -[~` b `|` a]ocomplK ocomplU ocomplK eq_sym;
  apply/eqP/le_joinIO/leIl.
rewrite -dual_commute_eq /dual_commute=>/eqP{2}->.
by rewrite [X in _ == X]meetC meetA joinKIC meetC eqxx.
Qed.

Lemma commute_char1 a b : ((a `|` ~` b) `&` b == (b `|` ~` a) `&` a) = a _C_ b.
Proof.
apply/Bool.eq_iff_eq_true; split;
first by move=>/eqP P;
rewrite -commute_char2 -{2}[b]meetxx meetA P meetC meetA joinKI meetC eqxx.
move=>P; move: P {+}P; rewrite -{1}commute_char2=>/eqP->.
by rewrite commuteC -commute_char2=>/eqP->; rewrite meetC eqxx.
Qed.

Lemma commute_char3 a b : ((b `|` ~` a) `&` a == a `&` b) = a _C_ b.
Proof. by rewrite [a `&` b]meetC commute_char2 commuteC. Qed.

Lemma commute_char4 a b : ((a `&` ~` b) `|` b == (b `&` ~` a) `|` a) = a _C_ b.
Proof.
by rewrite -(inj_eq ocompl_inj) !ocomplU !ocomplI commute_char1 commuteOO.
Qed.

Lemma commute_char5 a b : ((a `&` ~` b) `|` b == a `|` b) = a _C_ b.
Proof.
by rewrite -(inj_eq ocompl_inj) !ocomplU !ocomplI commute_char2 commuteOO.
Qed.

Lemma commute_char6 a b : ((b `&` ~` a) `|` a == a `|` b) = a _C_ b.
Proof.
by rewrite -(inj_eq ocompl_inj) !ocomplU !ocomplI commute_char3 commuteOO.
Qed.

Lemma meetxUr a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  a `&` (b1 `|` b2) = (a `&` b1) `|` (a `&` b2).
Proof.
move=>P1 P2; set s := a `&` (b1 `|` b2).
pose t := ~` (a `&` b1 `|` a `&` b2).
rewrite -[RHS]ocomplK -/t; apply/le_meet0_eqO.
rewrite /t /s ocomplK leUx; apply/andP; split; apply/leI2=>//.
apply/leUl. apply/leUr.
rewrite /s /t ocomplU !ocomplI meetACA.
move: P1; rewrite commuteC -commuteOx -commute_char2 meetC joinC=>/eqP->.
rewrite meetACA.
move: P2; rewrite commuteC -commuteOx -commute_char2 meetC joinC=>/eqP->.
by rewrite meetACA -ocomplU meetA meetOx meet0x.
Qed.

Lemma meetUrxl a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  b1 `&` (a `|` b2) = (b1 `&` a) `|` (b1 `&` b2).
Proof.
move=>P1 P2; set s := b1 `&` (a `|` b2).
pose t := ~` (b1 `&` a `|` b1 `&` b2).
rewrite -[RHS]ocomplK -/t; apply/le_meet0_eqO.
rewrite /t /s ocomplK leUx; apply/andP; split; apply/leI2=>//.
apply/leUl. apply/leUr.
rewrite /s /t ocomplU !ocomplI meetACA.
move: P1; rewrite -commuteOx -commute_char2 meetC joinC=>/eqP->.
rewrite meetACA.
move: P2; rewrite commuteC -commutexO -commute_char2
  ocomplK meetC joinC=>/eqP->.
by rewrite meetACA -ocomplI [b2 `&` _]meetC meetC -meetA meetOx meetx0.
Qed.

Lemma meetUrxr a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  b1 `&` (b2 `|` a) = (b1 `&` b2) `|` (b1 `&` a).
Proof. by move=>P1 P2; rewrite joinC meetUrxl// joinC. Qed.

Lemma Foulis_Holland_meetUr a b c : 
  ((a _C_ b) && (a _C_ c)) || ((b _C_ a) && (b _C_ c)) ||
  ((c _C_ a) && (c _C_ b)) -> 
    a `&` (b `|` c) = (a `&` b) `|` (a `&` c).
Proof.
move=>/orP[/orP[]|]/andP[];
[apply: meetxUr | apply: meetUrxl | apply: meetUrxr].
Qed.

Lemma Foulis_Holland_joinUr a b c : 
  ((a _C_ b) && (a _C_ c)) || ((b _C_ a) && (b _C_ c)) ||
  ((c _C_ a) && (c _C_ b)) -> 
    a `|` (b `&` c) = (a `|` b) `&` (a `|` c).
Proof.
move: (@Foulis_Holland_meetUr (~` a) (~` b) (~` c));
by rewrite !commuteOO -!(ocomplU, ocomplI)=>P /P /ocompl_inj.
Qed.

Lemma Foulis_Holland_meetUl a b c : 
  ((a _C_ b) && (a _C_ c)) || ((b _C_ a) && (b _C_ c)) ||
  ((c _C_ a) && (c _C_ b)) -> 
    (b `|` c) `&` a = (b `&` a) `|` (c `&` a).
Proof. by move=>/Foulis_Holland_meetUr; rewrite ![a `&` _]meetC. Qed.

Lemma Foulis_Holland_joinUl a b c : 
  ((a _C_ b) && (a _C_ c)) || ((b _C_ a) && (b _C_ c)) ||
  ((c _C_ a) && (c _C_ b)) -> 
    (b `&` c) `|` a = (b `|` a) `&` (c `|` a).
Proof. by move=>/Foulis_Holland_joinUr; rewrite ![a `|` _]joinC. Qed.

Lemma meetUlx a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  (b1 `|` b2) `&` a = (b1 `&` a) `|` (b2 `&` a).
Proof. by move=>P1 P2; rewrite meetC meetxUr// ![a `&` _]meetC. Qed.

Lemma meetxlUl a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  (a `|` b2) `&` b1 = (a `&` b1) `|` (b2 `&` b1).
Proof. by move=>P1 P2; rewrite meetC meetUrxl// ![b1 `&` _]meetC. Qed.

Lemma meetxrUl a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  (b2 `|` a) `&` b1 = (b2 `&` b1) `|` (a `&` b1).
Proof. by move=>P1 P2; rewrite joinC meetxlUl// joinC. Qed.

Lemma joinxIr a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  a `|` (b1 `&` b2) = (a `|` b1) `&` (a `|` b2).
Proof. by move=>P1 P2; rewrite Foulis_Holland_joinUr// P1 P2. Qed.

Lemma joinIrxl a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  b1 `|` (a `&` b2) = (b1 `|` a) `&` (b1 `|` b2).
Proof. by move=>P1 P2; rewrite Foulis_Holland_joinUr// P1 P2 orbT. Qed.

Lemma joinIrxr a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  b1 `|` (b2 `&` a) = (b1 `|` b2) `&` (b1 `|` a).
Proof. by move=>P1 P2; rewrite Foulis_Holland_joinUr// P1 P2 !orbT. Qed.

Lemma joinIlx a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  (b1 `&` b2) `|` a = (b1 `|` a) `&` (b2 `|` a).
Proof. by move=>P1 P2; rewrite joinC joinxIr// ![a `|` _]joinC. Qed.

Lemma joinxlIl a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  (a `&` b2) `|` b1 = (a `|` b1) `&` (b2 `|` b1).
Proof. by move=>P1 P2; rewrite joinC joinIrxl// ![b1 `|` _]joinC. Qed.

Lemma joinxrIl a b1 b2 : a _C_ b1 -> a _C_ b2 -> 
  (b2 `&` a) `|` b1 = (b2 `|` b1) `&` (a `|` b1).
Proof. by move=>P1 P2; rewrite meetC joinxlIl// meetC. Qed.

Lemma commutexU a b c : a _C_ b -> a _C_ c -> a _C_ (b `|` c).
Proof.
move=>P1 P2.
rewrite commuteC /commute meetC [_ `&` ~` a]meetC !Foulis_Holland_meetUr.
rewrite joinACA ![a `&` _]meetC ![~` a `&` _]meetC;
by move: P1 P2; rewrite ![a _C_ _]commuteC /commute=>/eqP<-/eqP<-.
all: by rewrite ?commuteOx P1 P2.
Qed.

Lemma commutexI a b c : a _C_ b -> a _C_ c -> a _C_ (b `&` c).
Proof.
by move=>P1 P2; rewrite -commutexO ocomplI;
apply: commutexU; rewrite commutexO.
Qed.

Lemma commutexOx x : x _C_ ~` x.
Proof. by rewrite commutexO commutexx. Qed.

Lemma commuteOxx x : ~` x _C_ x.
Proof. by rewrite commuteC commutexOx. Qed.

Lemma commutexIl x y : x _C_ (x `&` y).
Proof. by rewrite commuteC; apply/le_commute/leIl. Qed.

Lemma commuteIlx x y : (x `&` y) _C_ x.
Proof. by rewrite commuteC commutexIl. Qed.

Lemma commutexIr x y : x _C_ (y `&` x).
Proof. by rewrite meetC commutexIl. Qed.

Lemma commuteIrx x y : (y `&` x) _C_ x.
Proof. by rewrite meetC commuteIlx. Qed.

Lemma commutexUl x y : x _C_ (x `|` y).
Proof. by apply/le_commute/leUl. Qed.

Lemma commuteUlx x y : (x `|` y) _C_ x.
Proof. by rewrite commuteC commutexUl. Qed.

Lemma commutexUr x y : x _C_ (y `|` x).
Proof. by rewrite joinC commutexUl. Qed.

Lemma commuteUrx x y : (y `|` x) _C_ x.
Proof. by rewrite joinC commuteUlx. Qed.

(* sasaki hook/implication and sasaki projection *)
(* short notation : shook : H   sproj : J *)
Lemma shookO x y : ~` (x `=>` y) = (x `&&` ~` y).
Proof. by rewrite /sasaki_hook ocomplU ocomplI ocomplK. Qed.

Lemma sprojO x y : ~` (x `&&` y) = (x `=>` ~` y).
Proof. by rewrite -[RHS]ocomplK shookO ocomplK. Qed.

Lemma shookx1 x : x `=>` \top = \top.
Proof. by rewrite /sasaki_hook meetx1 joinOx. Qed.

Lemma shookx0 x : x `=>` \bot = ~` x.
Proof. by rewrite /sasaki_hook meetx0 joinx0. Qed.

Lemma shook0x x : \bot `=>` x = \top.
Proof. by rewrite /sasaki_hook meet0x joinOx. Qed.

Lemma shook1x x : \top `=>` x = x.
Proof. by rewrite /sasaki_hook meet1x ocompl1 join0x. Qed.

Lemma sprojx0 x : x `&&` \bot = \bot.
Proof. by rewrite /sasaki_projection joinx0 meetxO. Qed.

Lemma sprojx1 x : x `&&` \top = x.
Proof. by rewrite /sasaki_projection joinx1 meetx1. Qed.

Lemma sproj0x x : \bot `&&` x = \bot.
Proof. by rewrite /sasaki_projection meet0x. Qed.

Lemma sproj1x x : \top `&&` x = x.
Proof. by rewrite /sasaki_projection ocompl1 join0x meet1x. Qed.

Lemma shookxx x : x `=>` x = \top.
Proof. by rewrite /sasaki_hook meetxx joinOx. Qed.

Lemma sprojxx x : x `&&` x = x.
Proof. by rewrite /sasaki_projection joinOx meetx1. Qed.

Lemma sprojUr x y1 y2 : (x `&&` (y1 `|` y2)) = (x `&&` y1) `|` (x `&&` y2).
Proof.
rewrite /sasaki_projection -meetxUr.
by rewrite joinACA joinxx.
all: by rewrite -commutexO ocomplU ocomplK commuteC le_commute// leIl.
Qed.

Lemma shookIr x y1 y2 : (x `=>` (y1 `&` y2)) = (x `=>` y1) `&` (x `=>` y2).
Proof. by apply/ocompl_inj; rewrite shookO !ocomplI sprojUr !shookO. Qed.

Lemma sproj_joins x I (r : seq I) (P : pred I) (Y : I -> T) :
  (x `&&` (\join_(i <- r | P i) Y i)) = \join_(i <- r | P i) (x `&&` Y i).
Proof.
elim/big_rec2: _; first by rewrite sprojx0.
by move=>i y1 y2 Pi <-; rewrite sprojUr.
Qed.

Lemma shook_meets x I (r : seq I) (P : pred I) (Y : I -> T) :
  (x `=>` (\meet_(i <- r | P i) Y i)) = \meet_(i <- r | P i) (x `=>` Y i).
Proof.
elim/big_rec2: _; first by rewrite shookx1.
by move=>i y1 y2 Pi <-; rewrite shookIr.
Qed.

Lemma leJr x y1 y2 : y1 <= y2 -> (x `&&` y1) <= (x `&&` y2).
Proof. by move=>P; rewrite /sasaki_projection leI2// leU2. Qed.

Lemma leHr x y1 y2 : y1 <= y2 -> (x `=>` y1) <= (x `=>` y2).
Proof. by move=>P; rewrite /sasaki_hook leU2// leI2. Qed.

Lemma leJl x y : x `&&` y <= x.
Proof. by rewrite /sasaki_projection leIl. Qed.

Lemma leEshook x y : (x <= y) = (x `=>` y == \top).
Proof.
apply/Bool.eq_iff_eq_true; split; rewrite /sasaki_hook.
by rewrite leEmeet=>/eqP->; rewrite joinOx eqxx.
move=>/eqP/(f_equal (meet x)); 
rewrite meetx1 meetUrxl ?commuteOxx// ?commuteOx ?commutexIl//.
by rewrite meetxO join0x meetA meetxx leEmeet=>->; rewrite eqxx.
Qed.

(* compatible import-export law *)
Lemma commute_leIx x y z : x _C_ y -> (x `&` y <= z) = (x <= (y `=>` z)).
Proof.
move=>P; apply/Bool.eq_iff_eq_true; rewrite !leEmeet; split.
  rewrite /sasaki_hook meetUrxl.
  by rewrite meetA=>/eqP->; rewrite joinC eq_sym.
  by rewrite commuteOx commuteC.
  by rewrite commuteOx commutexIl.
move=>/eqP/(f_equal (meet ^~ y)).
rewrite meetAC -meetA /sasaki_hook meetxUr ?commutexOx ?commutexIl//.
by rewrite meetxO join0x meetC meetA meetxx meetC meetA=>->; rewrite eqxx.
Qed.

Lemma commuteHE x y : x _C_ y -> x `=>` y = ~` x `|` y.
Proof.
by move=>P; rewrite /sasaki_hook joinIrxl// ?commutexOx// joinOx meet1x.
Qed.

Lemma commuteJE x y : x _C_ y -> x `&&` y = x `&` y.
Proof.
by move=>P; rewrite /sasaki_projection meetxUr// ?commutexOx// meetxO join0x.
Qed.

Lemma eq_shookr x y : (x `=>` y == y) = (~` x <= y).
Proof.
apply/Bool.eq_iff_eq_true; split.
by move=>/eqP<-; apply/leUl.
move=>P; rewrite commuteHE. by rewrite -leEjoin.
by rewrite -commuteOx; apply/le_commute.
Qed.

Lemma eq_shookl x y : (x `=>` y == ~` x) = (x `&` y == \bot).
Proof.
apply/Bool.eq_iff_eq_true; split.
rewrite /sasaki_hook eq_joinl=>/(leI2 (lexx x)).
by rewrite meetA meetxx meetxO lex0.
by rewrite /sasaki_hook=>/eqP->; rewrite joinx0 eqxx.
Qed.

Lemma eq_sprojr x y : (x `&&` y == y) = (y <= x).
Proof.
by rewrite -{1 2}[y]ocomplK -shookO (inj_eq ocompl_inj) eq_shookr leO.
Qed.

Lemma eq_sprojl x y : (x `&&` y == x) = (x `&` ~` y == \bot).
Proof. by rewrite -eq_shookl -(inj_eq ocompl_inj) sprojO. Qed.

Lemma eq_sproj0 x y :
  (x `&&` y == \bot)%O = (x <= ~` y)%O.
Proof. by rewrite -(inj_eq ocompl_inj) sprojO ocompl0 -leEshook. Qed.

Lemma sprojxHl x y : x `&&` (x `=>` y) = x `&` y.
Proof.
rewrite /sasaki_hook /sasaki_projection meetxUr.
rewrite meetxO join0x meetxUr.
by rewrite meetxO join0x meetA meetxx.
all: by rewrite ?commutexU// ?commutexIl// commutexOx.
Qed.

Lemma shook_compK x y z : 
  y `=>` (x `=>` ((x `=>` y) `=>` z)) = (x `=>` ((x `=>` y) `=>` z)).
Proof.
apply/eqP; rewrite eq_shookr leOx !shookO.
by apply: (le_trans (leJr _ (leJl _ _))); rewrite sprojxHl leIr.
Qed.

Lemma sprojxO x : x `&&` ~` x = \bot.
Proof. by rewrite /sasaki_projection joinxx meetxO. Qed.

Lemma sprojOx x : ~` x `&&` x = \bot.
Proof. by rewrite -{2}[x]ocomplK sprojxO. Qed.

Lemma shookOx x : ~` x `=>` x = x.
Proof. by rewrite /sasaki_hook meetOx joinx0 ocomplK. Qed.

Lemma shookxO x : x `=>` ~` x = ~` x.
Proof. by rewrite -[RHS]shookOx ocomplK. Qed. 

End OModularLatticeTheory.

Section OModularLatticeF2.
Variable (disp : unit) (T : oModularLatticeType disp) (a b : T).

Inductive M02 := M02_0 | M02_1 | M02_a | M02_b | M02_aO | M02_bO.
Definition M02_ocompl (x : M02) : M02 :=
  match x with
  | M02_0 => M02_1
  | M02_1 => M02_0
  | M02_a => M02_aO
  | M02_aO => M02_a
  | M02_b => M02_bO
  | M02_bO => M02_b
  end.
Definition M02_meet (x y : M02) : M02 :=
  match x with
  | M02_0 => M02_0
  | M02_1 => y
  | M02_a => match y with
             | M02_1 | M02_a => M02_a
             | _ => M02_0
             end
  | M02_b => match y with
             | M02_1 | M02_b => M02_b
             | _ => M02_0
             end
  | M02_aO => match y with
             | M02_1 | M02_aO => M02_aO
             | _ => M02_0
             end
  | M02_bO => match y with
             | M02_1 | M02_bO => M02_bO
             | _ => M02_0
             end
  end.
Definition M02_join (x y : M02) : M02 :=
  M02_ocompl (M02_meet (M02_ocompl x) (M02_ocompl y)).

Local Notation "0" := false.
Local Notation "1" := true.
Local Notation "'M0'" := M02_0.
Local Notation "'M1'" := M02_1.
Local Notation "'A'" := M02_a.
Local Notation "'B'" := M02_b.
Local Notation "'A''" := M02_aO.
Local Notation "'B''" := M02_bO.

Definition M81 := 
  (a `|` b) `&` (a `|` ~` b) `&` (~` a `|` b) `&` (~` a `|` ~` b).

Definition M02_gen1 (x : M02) : T :=
  match x with
  | M0 => \bot | A => a | A' => ~` a | B => b | B' => ~` b | M1 => \top
  end.
Definition M02_gen (x : M02) : T := M02_gen1 x `&` M81.
  (* match x with
  | M0 => \bot
  | A => a `&` (~` a `|` b) `&` (~` a `|` ~` b)
  | B => b `&` (a `|` ~` b) `&` (~` a `|` ~` b)
  | B' => ~` b `&` (a `|` b) `&` (~` a `|` b)
  | A' => ~` a `&` (a `|` b) `&` (a `|` ~` b)
  | M1 => (a `|` b) `&` (a `|` ~` b) `&` (~` a `|` b) `&` (~` a `|` ~` b)
  end. *)

Lemma commutex0 (e : T) : e _C_ \bot.
Proof. by rewrite /commute ocompl0 meetx1 meetx0 join0x. Qed.
Lemma commute0x (e : T) : \bot _C_ e.
Proof. by rewrite commuteC commutex0. Qed.
Lemma commutex1 (e : T) : e _C_ \top.
Proof. by rewrite -commutexO ocompl1 commutex0. Qed.
Lemma commute1x (e : T) : \top _C_ e.
Proof. by rewrite commuteC commutex1. Qed.
Lemma commuteaM81 : a _C_ M81.
Proof.
by rewrite !commutexI// ?commutexUl ?commutexUr//
  -commuteOx ?ocomplK ?commutexUl ?commutexUr.
Qed.
Lemma commutebM81 : b _C_ M81.
Proof.
by rewrite !commutexI// ?commutexUl ?commutexUr//
  -commuteOx ?ocomplK ?commutexUl ?commutexUr.
Qed.

Lemma M02_gen_commute (x : M02) : 
  M02_gen1 x _C_ M81.
Proof.
by case: x; rewrite ?commute0x ?commute1x ?commuteOx ?commuteaM81 ?commutebM81.
Qed.

Lemma M02_gen_ocompl m :
  M02_gen (M02_ocompl m) = ~` (M02_gen m) `&` M81.
Proof.
rewrite ocomplI meetxlUl ?commuteOx ?commutexO ?M02_gen_commute //
  meetOx joinx0.
by case: m; rewrite ?(ocomplK, ocompl0, ocompl1).
Qed.

Definition B4_gen_base s s1 s2 :=
  if s then
    (if s1 then ~` a else a) `&` (if s2 then ~` b else b)
  else \bot.
Definition B4_gen (s1 s2 s3 s4 : bool) :=
  B4_gen_base s1 0 0 `|` B4_gen_base s2 0 1 `|` 
  B4_gen_base s3 1 0 `|` B4_gen_base s4 1 1.
  (* match s1, s2, s3, s4 with
  | 0, 0, 0, 0 => \bot
  | 1, 0, 0, 0 => (a `&` b)
  | 0, 1, 0, 0 => (a `&` ~` b)
  | 0, 0, 1, 0 => (~` a `&` b)
  | 0, 0, 0, 1 => (~` a `&` ~` b)
  | 1, 1, 0, 0 => (a `&` b) `|` (a `&` ~` b)
  | 1, 0, 1, 0 => (a `&` b) `|` (~` a `&` b)
  | 1, 0, 0, 1 => (a `&` b) `|` (~` a `&` ~` b)
  | 0, 1, 1, 0 => (a `&` ~` b) `|` (~` a `&` b)
  | 0, 1, 0, 1 => (a `&` ~` b) `|` (~` a `&` ~` b)
  | 0, 0, 1, 1 => (~` a `&` b) `|` (~` a `&` ~` b)
  | 1, 1, 1, 0 => (a `&` b) `|` (a `&` ~` b) `|` (~` a `&` b)
  | 1, 1, 0, 1 => (a `&` b) `|` (a `&` ~` b) `|` (~` a `&` ~` b)
  | 1, 0, 1, 1 => (a `&` b) `|` (~` a `&` b) `|` (~` a `&` ~` b)
  | 0, 1, 1, 1 => (a `&` ~` b) `|` (~` a `&` b) `|` (~` a `&` ~` b)
  | 1, 1, 1, 1 => (a `&` b) `|` (a `&` ~` b) `|` (~` a `&` b) `|` (~` a `&` ~` b)
  end. *)
Lemma B4_gen_rev s1 s2 s3 s4 :
  B4_gen s1 s2 s3 s4
  = B4_gen_base s4 1 1 `|` B4_gen_base s3 1 0 `|`
    B4_gen_base s2 0 1 `|` B4_gen_base s1 0 0.
Proof.
  rewrite /B4_gen joinC -!joinA; f_equal;
  rewrite joinC !joinA; f_equal;
  by rewrite joinC.
Qed.

Lemma B4_gen_base_join s1 s2 t1 t2 :
  B4_gen_base s1 t1 t2 `|` B4_gen_base s2 t1 t2 =
    B4_gen_base (s1 || s2) t1 t2.
Proof.
case: s1; last by rewrite /= join0x.
case: s2; last by rewrite /= joinx0.
by rewrite joinxx.
Qed.

Lemma B4_gen_base_meet s s1 s2 t t1 t2 :
  B4_gen_base s s1 s2 `&` B4_gen_base t t1 t2
= B4_gen_base ((s1==t1) && (s2==t2) && s && t) s1 s2.
Proof.
move: s t => [] []; rewrite ?(andbT, andbF) ?(meet0x, meetx0) //.
by move: s1 t1 s2 t2 => [] [] [] []; rewrite ?(andTb, andFb) ?meetxx //=
  meetACA (meetxO, meetOx) (meet0x, meetx0).
Qed.

Lemma B4_gen_base_meetO1 s1 s2 t1 t2 :
  ~` B4_gen_base 1 s1 s2 `&` B4_gen_base 1 t1 t2
= B4_gen_base ((s1 != t1) || (s2 != t2)) t1 t2.
Proof.
move: s1 t1 s2 t2 => [] [] [] []; rewrite ?meetOx //= ?ocomplI ?ocomplK
  meetUlx ?commuteIlx ?commuteIrx//;
(try by rewrite commutexO (commuteIlx, commuteIrx));
(try by rewrite -commutexO (commuteIlx, commuteIrx));
by rewrite !meetA ?(meetOx, meetxO, meetxx, meet1x, meet0x) ?join0x
  -meetA meetCA (meetOx, meetxO, meetxx) ?(meetx0, joinx0, joinxx).
Qed.

Lemma B4_gen_join s1 s2 s3 s4 t1 t2 t3 t4 :
  B4_gen s1 s2 s3 s4 `|` B4_gen t1 t2 t3 t4 =
    B4_gen (s1 || t1) (s2 || t2) (s3 || t3) (s4 || t4).
Proof.
rewrite (B4_gen_rev t1 _ _ _) /B4_gen;
do ?(rewrite !joinA joinC !joinA orbC B4_gen_base_join -!joinA; f_equal);
exact: B4_gen_base_join.
Qed.

Lemma commute_B4_gen_base s s1 s2 t t1 t2 :
  B4_gen_base s s1 s2 _C_ B4_gen_base t t1 t2.
Proof.
case: s=>/=; last by apply: commute0x.
case: t=>/=; last by apply: commutex0.
case: s1; case: s2; case: t1; case: t2; try apply: commutexx.
1-3, 5,6, 9: rewrite commuteC.
all: try (rewrite /= -commutexO ocomplI !ocomplK;
  apply/le_commute/(le_trans (y := a));
  [apply/leIl | apply/leUl]);
  try (rewrite /= -commutexO ocomplI !ocomplK;
  apply/le_commute/(le_trans (y := b)); 
  [apply/leIr | apply/leUr]).
Qed.

Lemma commute_M81_B4_gen_base s s1 s2 :
  M81 _C_ B4_gen_base s s1 s2.
Proof.
by move: s s1 s2 => [] [] []; rewrite ?commutex0 ?commutexI ?commutexO//
  commuteC ?commuteaM81 ?commutebM81.
Qed.

Lemma commute_M81_B4_gen s1 s2 s3 s4:
  M81 _C_ B4_gen s1 s2 s3 s4.
Proof. by rewrite /B4_gen !commutexU ?commute_M81_B4_gen_base. Qed.

Lemma meetOB4_gen_base_M81 s s1 s2 :
  ~` B4_gen_base s s1 s2 `&` M81 = M81.
Proof.
case: s; last by rewrite ocompl0 meet1x.
move: s1 s2 => [] []; rewrite ocomplI ?ocomplK /M81.
  by rewrite !meetA meetxx.
  by rewrite !meetA; f_equal; f_equal; rewrite meetAC meetxx meetC.
  by rewrite !meetA; f_equal; rewrite (meetC (~` a `|` b)) -!meetA; f_equal;
    rewrite meetCA meetxx.
  by rewrite meetC -!meetA meetxx.
Qed.

Lemma leM81_OB4_gen (s1 s2 s3 s4 : bool) :
  ~` B4_gen s1 s2 s3 s4 `&` M81 = M81.
Proof. 
by rewrite /B4_gen !ocomplU -!meetA !meetOB4_gen_base_M81.
Qed.

Lemma leOM81_OM02_gen (m : M02) :
  ~` M02_gen m `&` ~` M81 = ~` M81.
Proof.
by rewrite /M02_gen ocomplI joinIK.
Qed.

Lemma commute_B4_gen s1 s2 s3 s4 t1 t2 t3 t4 :
  B4_gen s1 s2 s3 s4 _C_ B4_gen t1 t2 t3 t4.
Proof.
rewrite /B4_gen; (do ? apply: commutexU); rewrite commuteC;
do ? apply: commutexU; apply: commute_B4_gen_base.
Qed.

Lemma ocomplM81 :
  ~` M81 = B4_gen 1 1 1 1.
Proof.
by rewrite /M81 B4_gen_rev /B4_gen_base !ocomplI !ocomplU !ocomplK.
Qed.

Lemma meetB4gb00_B4g s s1 s2 s3 s4:
  B4_gen_base s 0 0 `&` B4_gen s1 s2 s3 s4 = B4_gen_base (s && s1) 0 0.
Proof.
by rewrite /B4_gen !meetxUr ?commutexU ?commute_B4_gen_base//
  !B4_gen_base_meet !joinx0.
Qed.

Lemma meetB4gb01_B4g s s1 s2 s3 s4:
  B4_gen_base s 0 1 `&` B4_gen s1 s2 s3 s4 = B4_gen_base (s && s2) 0 1.
Proof.
by rewrite /B4_gen !meetxUr ?commutexU ?commute_B4_gen_base//
  !B4_gen_base_meet !joinx0 !join0x.
Qed.

Lemma meetB4gb10_B4g s s1 s2 s3 s4:
  B4_gen_base s 1 0 `&` B4_gen s1 s2 s3 s4 = B4_gen_base (s && s3) 1 0.
Proof.
by rewrite /B4_gen !meetxUr ?commutexU ?commute_B4_gen_base//
  !B4_gen_base_meet !joinx0 !join0x.
Qed.

Lemma meetB4gb11_B4g s s1 s2 s3 s4:
  B4_gen_base s 1 1 `&` B4_gen s1 s2 s3 s4 = B4_gen_base (s && s4) 1 1.
Proof.
by rewrite /B4_gen !meetxUr ?commutexU ?commute_B4_gen_base//
  !B4_gen_base_meet !joinx0 !join0x.
Qed.

Definition meetB4gb_B4g :=
  (meetB4gb00_B4g, meetB4gb01_B4g, meetB4gb10_B4g, meetB4gb11_B4g).

Lemma B4_gen_ocompl (s1 s2 s3 s4 : bool) :
  B4_gen (~~ s1) (~~ s2) (~~ s3) (~~ s4) = ~` (B4_gen s1 s2 s3 s4) `&` ~` M81.
Proof.
rewrite [LHS]/B4_gen.
have ->: B4_gen_base (~~ s1) 0 0 = ~` (B4_gen s1 1 1 1) `&` ~` M81
  by case: s1; first (by rewrite ocomplM81 meetOx);
  rewrite ocomplM81 {1}/B4_gen join0x !ocomplU B4_gen_rev -!joinA -!meetA
  meetxUr ?meetOx ?join0x ?commuteOx ?commutexU ?commute_B4_gen_base //
    !meetA [(_ `&` _) `&` ~`_]meetC -!meetA
  meetxUr ?meetOx ?join0x ?commuteOx ?commutexU ?commute_B4_gen_base //
    !meetA [(_ `&` _) `&` ~`_]meetC -!meetA
  meetxUr ?meetOx ?join0x ?commuteOx ?commute_B4_gen_base// !B4_gen_base_meetO1.
have ->: B4_gen_base (~~ s2) 0 1 = ~` (B4_gen 1 s2 1 1) `&` ~` M81
  by case: s2; first (by rewrite ocomplM81 meetOx);
  rewrite ocomplM81 {1}/B4_gen joinx0 !ocomplU B4_gen_rev -!joinA -!meetA
  meetxUr ?meetOx ?join0x ?commuteOx ?commutexU ?commute_B4_gen_base //
    !meetA [(_ `&` _) `&` ~`_]meetC -!meetA
  meetxUr ?meetOx ?join0x ?commuteOx ?commutexU ?commute_B4_gen_base //
    joinC [_ `&` (_ `&` (_ `|` _))]meetCA
  meetxUr ?meetOx ?join0x ?commuteOx ?commute_B4_gen_base// !B4_gen_base_meetO1.
have ->: B4_gen_base (~~ s3) 1 0 = ~` (B4_gen 1 1 s3 1) `&` ~` M81
  by case: s3; first (by rewrite ocomplM81 meetOx);
  rewrite ocomplM81 {1}/B4_gen joinx0 !ocomplU B4_gen_rev -!joinA -!meetA
  meetxUr ?meetOx ?join0x ?commuteOx ?commutexU ?commute_B4_gen_base //
    joinC [_ `&` (_ `&` (_ `|` _))]meetCA -joinA
  meetxUr ?meetOx ?join0x ?commuteOx ?commutexU ?commute_B4_gen_base //
    meetA meetCA [~` _ `&` ~` _]meetC -!meetA
  meetxUr ?meetOx ?join0x ?commuteOx ?commute_B4_gen_base// !B4_gen_base_meetO1.
have ->: B4_gen_base (~~ s4) 1 1 = ~` (B4_gen 1 1 1 s4) `&` ~` M81
  by case: s4; first (by rewrite ocomplM81 meetOx);
  rewrite ocomplM81 {1}/B4_gen joinx0 !ocomplU B4_gen_rev -!joinA joinC
    -!joinA -!meetA meetxUr ?meetOx ?join0x ?commuteOx ?commutexU
    ?commute_B4_gen_base // !meetA [(_ `&` _) `&` ~`_]meetC -!meetA
    meetxUr ?meetOx ?join0x ?commuteOx ?commutexU ?commute_B4_gen_base //
    !meetA [(_ `&` _) `&` ~`_]meetC -!meetA meetxUr ?meetOx
    ?join0x ?commuteOx ?commute_B4_gen_base// !B4_gen_base_meetO1.
rewrite -!ocomplU -!ocomplI; f_equal;
rewrite -!(joinIlx (a:=M81)) ?commutexI ?commute_M81_B4_gen //; f_equal.
rewrite {1 5}/B4_gen.
do ?(rewrite meetUlx ?commutexU ?(commutexI(b:= B4_gen_base _ _ _)) ?commutexU
  1?commuteC ?commutexU ?(commutexI(b:= B4_gen_base _ _ _)) ?commutexU
  ?commute_B4_gen_base//);
rewrite 1?commuteC 2?commutexI ?commutexU ?commute_B4_gen_base//;
f_equal; f_equal; f_equal; by rewrite !meetB4gb_B4g !andbT ?andTb.
Qed.

Inductive M02_b4 := M02_B4 of M02 & bool & bool & bool & bool.
Definition M02_b4_ocompl (x : M02_b4) : M02_b4 :=
  match x with
  | M02_B4 m b1 b2 b3 b4
    => M02_B4 (M02_ocompl m) (~~ b1) (~~ b2) (~~ b3) (~~ b4)
  end.
Definition M02_b4_meet (x y : M02_b4) : M02_b4 :=
  match x, y with
  | M02_B4 m1 b1 b2 b3 b4, M02_B4 m2 c1 c2 c3 c4
    => M02_B4 (M02_meet m1 m2) (andb b1 c1) (andb b2 c2)
                               (andb b3 c3) (andb b4 c4)
  end.
Definition M02_b4_join (x y : M02_b4) : M02_b4 :=
  match x, y with
  | M02_B4 m1 b1 b2 b3 b4, M02_B4 m2 c1 c2 c3 c4
    => M02_B4 (M02_join m1 m2) (orb b1 c1) (orb b2 c2)
                               (orb b3 c3) (orb b4 c4)
  end.

Definition exprT (x : M02_b4) :=
  match x with
  | M02_B4 M s1 s2 s3 s4 => (M02_gen M) `|` (B4_gen s1 s2 s3 s4)
  end.

Inductive OM_F2_Syntax :=
  | OM_F2_X | OM_F2_Y | OM_F2_ocompl of OM_F2_Syntax
  | OM_F2_meet of OM_F2_Syntax & OM_F2_Syntax
  | OM_F2_join of OM_F2_Syntax & OM_F2_Syntax.

Fixpoint eval_OM_F2_Syntax (x : OM_F2_Syntax) : T :=
  match x with
  | OM_F2_X => a
  | OM_F2_Y => b
  | OM_F2_ocompl x => ~` (eval_OM_F2_Syntax x)
  | OM_F2_meet x y => (eval_OM_F2_Syntax x) `&` (eval_OM_F2_Syntax y)
  | OM_F2_join x y => (eval_OM_F2_Syntax x) `|` (eval_OM_F2_Syntax y)
  end.

Lemma OM_F2_rule_X : a = eval_OM_F2_Syntax OM_F2_X.
Proof. by []. Qed.
Lemma OM_F2_rule_Y : b = eval_OM_F2_Syntax OM_F2_Y.
Proof. by []. Qed.
Lemma OM_F2_rule_ocompl x : ~` (eval_OM_F2_Syntax x) = 
  eval_OM_F2_Syntax (OM_F2_ocompl x).
Proof. by []. Qed.
Lemma OM_F2_rule_meet x1 x2 : 
  (eval_OM_F2_Syntax x1) `&` (eval_OM_F2_Syntax x2) = 
    eval_OM_F2_Syntax (OM_F2_meet x1 x2).
Proof. by []. Qed.
Lemma OM_F2_rule_join x1 x2 : 
  (eval_OM_F2_Syntax x1) `|` (eval_OM_F2_Syntax x2) = 
    eval_OM_F2_Syntax (OM_F2_join x1 x2).
Proof. by []. Qed.

Fixpoint compute_OM_F2_Syntax (x : OM_F2_Syntax) : M02_b4 :=
  match x with
  | OM_F2_X => M02_B4 M02_a true true false false
  | OM_F2_Y => M02_B4 M02_b true false true false
  | OM_F2_ocompl x => M02_b4_ocompl (compute_OM_F2_Syntax x)
  | OM_F2_meet x y
    => M02_b4_meet (compute_OM_F2_Syntax x) (compute_OM_F2_Syntax y)
  | OM_F2_join x y
    => M02_b4_join (compute_OM_F2_Syntax x) (compute_OM_F2_Syntax y)
  end.

Lemma ocompl_sound (x : M02_b4) :
  exprT (M02_b4_ocompl x) = ~` (exprT x).
Proof.
move: x=> [m s1 s2 s3 s4] /=.
rewrite M02_gen_ocompl B4_gen_ocompl [RHS]ocomplU.
have HC: (commute (~` M02_gen m `&` ~` B4_gen s1 s2 s3 s4) M81)
  by rewrite commuteC commutexI // commutexO;
  first (by rewrite /M02_gen commutexI ?commutexx // commuteC M02_gen_commute);
  rewrite /B4_gen !commutexU // commute_M81_B4_gen_base.
rewrite (eqP HC); f_equal.
by rewrite -meetA leM81_OB4_gen.
by rewrite (meetC (~` M02_gen m)) -meetA leOM81_OM02_gen.
Qed.

Lemma join_sound (x y : M02_b4) :
  exprT (M02_b4_join x y) = (exprT x) `|` (exprT y).
Proof.
case: x; case: y=>m1 s1 s2 s3 s4 m2 t1 t2 t3 t4/=.
rewrite joinACA /B4_gen; f_equal; last first.
  do 4 (rewrite 1?joinACA B4_gen_base_join; f_equal).
rewrite /M02_gen -meetUlx 1?commuteC ?M02_gen_commute//.
case: m1; case: m2=>/=;
rewrite ?join0x// ?join1x// ?joinx1// ?joinx0// ?joinxx// meet1x.
2,6,7,11: by rewrite ?joinxO ?joinOx meet1x.
1,2,5,6: rewrite joinC.
all: rewrite {2}/M81.
1,5: by rewrite !meetA meetxx.
3,6: by rewrite meetC -meetA meetxx.
all: rewrite /M81 meetA; f_equal; rewrite [RHS]meetC -!meetA; f_equal.
2,3: by rewrite meetxx.
all: by rewrite meetCA meetxx meetC.
Qed.

Lemma meet_sound (x y : M02_b4) :
  exprT (M02_b4_meet x y) = (exprT x) `&` (exprT y).
Proof.
rewrite -[RHS]ocomplK ocomplI -!ocompl_sound -join_sound -ocompl_sound.
f_equal. case: x=>m1 s1 s2 s3 s4; case: y=>m2 t1 t2 t3 t4.
rewrite/= !negb_or !negbK; f_equal.
by case: m1; case: m2.
Qed.

Lemma eval_sound x :
  eval_OM_F2_Syntax x = exprT (compute_OM_F2_Syntax x).
Proof.
elim: x.
- rewrite /= /M02_gen/= /B4_gen/= /M81 !meetA !joinKI !joinx0 
    joinC -[X in X `|` _]ocomplK ocomplU ![~` (a `&` _)]ocomplI 
    ocomplK meetC -[a `&` _ `&` _]meetA [a `&` _]meetC -/(sasaki_hook _ _).
  by symmetry; apply/eqP;
  rewrite eq_shookr ocomplI !ocomplU ocomplK leUx !leIl.
- rewrite /= /M02_gen/= /B4_gen/= /M81 -meetA meetACA !meetA !joinKIC
    !joinx0 joinC -[X in X `|` _]ocomplK ocomplU ![~` (_ `&` b)]ocomplI
    ocomplK meetC -[b `&` _ `&` _]meetA [b `&` _]meetC -/(sasaki_hook _ _).
  by symmetry; apply/eqP;
  rewrite eq_shookr ocomplI !ocomplU !ocomplK leUx !leIr.
- by move=>x /=; rewrite ocompl_sound=>->.
- by move=>x1 IH1 x2 IH2; rewrite /= meet_sound IH1 IH2.
- by move=>x1 IH1 x2 IH2; rewrite /= join_sound IH1 IH2.
Qed.

Lemma eval_eq_compute x1 x2 : 
  compute_OM_F2_Syntax x1 = compute_OM_F2_Syntax x2 -> 
    (eval_OM_F2_Syntax x1) = (eval_OM_F2_Syntax x2).
Proof. by rewrite !eval_sound=>->. Qed.

End OModularLatticeF2.

Ltac to_OM_F2_Syntax a b := 
let s := fresh "s" in
let t := fresh "t" in
set s := a;
set t := b;
rewrite 1?(OM_F2_rule_X s b) 1?(OM_F2_rule_Y a t) /t /s;
rewrite ?((OM_F2_rule_ocompl a b), (OM_F2_rule_meet a b), (OM_F2_rule_join a b)).

Ltac OM_autodec a b :=
  rewrite -?(meetOx a) -?(joinOx a) /sasaki_hook /sasaki_projection;
  to_OM_F2_Syntax a b; apply/eval_eq_compute/erefl.

(* <= >= == *)
Ltac OM_autocomp a b :=
  rewrite -?eq_meetl; apply /eqP; OM_autodec a b.

Section OModularLatticeF2Theory.
Variable (disp : unit) (T : oModularLatticeType disp).
Implicit Type (a b c : T).

(* Sasaki conjunction including two variables *)
Lemma ocomplJ a b : ~` (a `&&` b) = (a `=>` ~` b).
Proof. OM_autodec a b. Qed.

Lemma ocomplH a b : ~` (a `=>` b) = (a `&&` ~` b).
Proof. OM_autodec a b. Qed.

Lemma sprojxUyz a b c : a `&&` (b `|` c) = (a `&&` b) `|` (a `&&` c).
Proof. exact: sprojUr. Qed.

Lemma shookxIyz a b c : a `=>` (b `&` c) = (a `=>` b) `&` (a `=>` c).
Proof. exact: shookIr. Qed.

Lemma sprojxjoinsY a I (r : seq I) (P : pred I) (B : I -> T) :
  (a `&&` (\join_(i <- r | P i) B i)) = \join_(i <- r | P i) (a `&&` B i).
Proof. exact: sproj_joins. Qed.

Lemma shookxmeetsY a I (r : seq I) (P : pred I) (B : I -> T) :
  (a `=>` (\meet_(i <- r | P i) B i)) = \meet_(i <- r | P i) (a `=>` B i).
Proof. exact: shook_meets. Qed.

Lemma sprojJxyOx a b : (a `&&` b) `&&` ~` a = \bot.
Proof.
apply/eqP; rewrite commuteJE.
by rewrite -lex0 -(meetxO a) leI2// leJl.
rewrite commutexO; apply/le_commute/leJl.
Qed.

Lemma sprojxJOxy a b : a `&&` (~` a `&&` b) = \bot.
Proof. by apply/eqP; rewrite -lex0 -(sprojxO a) leJr// leJl. Qed.

Lemma sprojxJxy a b : a `&&` (a `&&` b) = (a `&&` b).
Proof. OM_autodec a b. Qed.

Lemma sprojxJyx a b : a `&&` (b `&&` a) = (a `&&` b).
Proof. OM_autodec a b. Qed.

Lemma sprojJxyx a b : (a `&&` b) `&&` a = (a `&&` b).
Proof. OM_autodec a b. Qed.

Lemma sprojJxyy a b : (a `&&` b) `&&` b = (a `&&` b).
Proof. OM_autodec a b. Qed.

Lemma sprojJxyJyx a b : (a `&&` b) `&&` (b `&&` a) = (a `&&` b).
Proof. OM_autodec a b. Qed.

Lemma sprojJxyOy a b : (a `&&` b) `&&` ~` b = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojJxyJxOy a b : (a `&&` b) `&&` (a `&&` ~` b) = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojxJyJxOy a b : a `&&` ( b `&&` (a `&&` ~` b)) = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojJxyJyOx a b : (a `&&` b) `&&` (b `&&` ~` a) = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojJxyJOyx a b : (a `&&` b) `&&` (~` b `&&` a) = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojJJxyOyx a b : ((a `&&` b) `&&` ~` b) `&&` a = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojJJxyOyy a b : ((a `&&` b) `&&` ~` b) `&&` b = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojxJyJOxOy a b :
  a `&&` ( b `&&` (~` a `&&` ~` b)) = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojJxJyOxOy a b :
  (a `&&` (b `&&` ~` a)) `&&` ~` b = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojJxJyOxy a b : (a `&&` (b `&&` ~` a)) `&&` b = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojxJJxyOy a b : a `&&` ((a `&&` b) `&&` ~` b) = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

Lemma sprojxJJyxOx a b : a `&&` ((b `&&` a) `&&` ~` a) = (a `&&` (b `&&` ~` a)).
Proof. OM_autodec a b. Qed.

(* Useful properties c.f. [Gabriëls et al. 2017] *)
Lemma joinIxOyJxy a b : (a `&` ~` b) `|` (a `&&` b) = a.
Proof. OM_autodec a b. Qed.

Lemma meetJxOyy a b :
  (a `&&` ~` b) `&` b = \bot.
Proof. OM_autodec a b. Qed.

Lemma leJxyx a b : a `&&` b <= a.
Proof. OM_autocomp a b. Qed.

Lemma sproj_leyx a b : b <= a -> (a `&&` b) = b.
Proof. by move=> Hab; apply /eqP; rewrite eq_sprojr. Qed.

Lemma sprojJxyz_lezy a b c : c <= b -> (a `&&` b) `&&` c = (a `&&` c).
Proof.
move=> Hbc; rewrite /sasaki_projection 
  ocomplI ocomplU ocomplK joinAC (meetUrxr(a :=  a `&` ~` b)).
have ->: a `&` (~` a `|` b) `&` (a `&` ~` b) = \bot by OM_autodec a b.
rewrite -meetA joinx0; f_equal; rewrite meet_r ?le_joinl//.
rewrite commutexI// ?commuteIlx//.
all: by rewrite -commutexO ocomplU ocomplK le_commute// le_meetl ?leO.
Qed.

Lemma sprojA_lezy a b c : c <= b -> a `&&` (b `&&` c) = (a `&&` b `&&` c).
Proof. by move=> Hbc; rewrite (sproj_leyx Hbc) sprojJxyz_lezy. Qed.

Lemma sprojxJyz_Cxy a b c : a _C_ b -> a `&&` (b `&&` c) = (a `&` b `&&` c).
Proof.
move=> Hab; rewrite /sasaki_projection joinIrxl;
first (by rewrite joinA -ocomplI meetA -{2}(commuteJE Hab));
by [rewrite commutexO commuteC | rewrite -commuteOx commutexUl].
Qed.

Lemma sprojA_Cxy a b c : a _C_ b -> a `&&` (b `&&` c) = (a `&&` b `&&` c).
Proof. by move=> Hab; rewrite (commuteJE Hab) sprojxJyz_Cxy. Qed.

(* Sasaki conjunction including three variables *)

Lemma sprojJxyJxz a b c : (a `&&` b) `&&` (a `&&` c) = ((a `&&` b) `&&` c).
Proof.
by rewrite /sasaki_projection !ocomplI !ocomplU !ocomplK; f_equal;
rewrite (joinC (~` a)) -!joinA; f_equal;
rewrite joinxIr 1?commuteC ?commuteUlx ?commutexOx//
  joinOx meet1x joinA joinxx.
Qed.

Lemma sprojJxyJzx a b c : (a `&&` b) `&&` (c `&&` a) = ((a `&&` b) `&&` c).
Proof. by rewrite -[LHS]sprojJxyJxz sprojxJyx sprojJxyJxz. Qed.

Lemma sprojxJJxyz a b c : a `&&` ((a `&&` b) `&&` c) = ((a `&&` b) `&&` c).
Proof. by apply /eqP; rewrite eq_sprojr (le_trans (leJl _ _) (leJl _ _)). Qed.

Lemma sprojJJxyzx a b c : ((a `&&` b) `&&` c) `&&` a = ((a `&&` b) `&&` c).
Proof.
by apply /eqP;
rewrite eq_sprojl /sasaki_projection meetC !meetA meetOx !meet0x.
Qed.

Lemma sprojJJxyzy a b c : ((a `&&` b) `&&` c) `&&` b = ((a `&&` b) `&&` c).
Proof.
apply /eqP; rewrite eq_sprojl /sasaki_projection (meetAC _ _ (~` b));
have ->: a `&` (~` a `|` b) `&` ~` b = \bot by OM_autodec a b.
by rewrite meet0x.
Qed.

Lemma sprojJJxyzz a b c : ((a `&&` b) `&&` c) `&&` c = ((a `&&` b) `&&` c).
Proof.
rewrite {1 2 4}/sasaki_projection; to_OM_F2_Syntax (a `&&` b) c;
apply/eval_eq_compute/erefl.
Qed.

Lemma sprojJxyJyz a b c : (a `&&` b) `&&` (b `&&` c) = (a `&&` (b `&&` c)).
Proof. by rewrite -sprojA_lezy ?sprojxJxy ?leJxyx. Qed.

(* extra *)
Lemma sprojxJyJyz a b c : a `&&` (b `&&` (b `&&` c)) = (a `&&` (b `&&` c)).
Proof. by rewrite sprojxJxy. Qed.

Lemma sprojJxJyzx a b c : (a `&&` (b `&&` c)) `&&` a = (a `&&` (b `&&` c)).
Proof. exact: sprojJxyx. Qed.

Lemma sprojJxJyzy a b c : (a `&&` (b `&&` c)) `&&` b = (a `&&` (b `&&` c)).
Proof.
apply /eqP; rewrite eq_sprojl /sasaki_projection -lex0;
have <-: a `&` (~` a `|` b ) `&` ~` b = \bot by OM_autodec a b.
by rewrite le_meetr ?le_meetl ?le_joinl// leIl.
Qed.

(*? Unable to prove *)
Lemma sprojxJJyxz a b c : a `&&` ((b `&&` a) `&&` c) = (a `&&` (b `&&` c)).
Proof. Abort.

Lemma sprojxJJyzx a b c : a `&&` ((b `&&` c) `&&` a) = (a `&&` (b `&&` c)).
Proof. exact: sprojxJyx. Qed.

Lemma sprojxJxJyz a b c : a `&&` (a `&&` (b `&&` c)) = (a `&&` (b `&&` c)).
Proof. exact: sprojxJxy. Qed.

(* Sasaki implication including two variables *)

Lemma shookxHxy a b : a `=>` (a `=>` b) = (a `=>` b).
Proof. OM_autodec a b. Qed.

Lemma shookxHOxy a b : a `=>` (~` a `=>` b) = \top.
Proof. OM_autodec a b. Qed.

Lemma shookxHyOx a b : a `=>` (b `=>` ~` a) = (a `=>` ~` b).
Proof. OM_autodec a b. Qed.

Lemma shookxHyx a b : a `=>` (b `=>` a) = ((a `&&` b) `=>` b).
Proof. OM_autodec a b. Qed.

Lemma shookHxyx a b : (a `=>` b) `=>` a = a.
Proof. OM_autodec a b. Qed.

Lemma shookHxyOx a b : (a `=>` b) `=>` ~` a = ~` a `|` ~` b.
Proof. OM_autodec a b. Qed.

Lemma shookHxyy a b : (a `=>` b) `=>` b = (~` a `=>` b).
Proof. OM_autodec a b. Qed.

Lemma shookHxyOy a b : (a `=>` b) `=>` ~` b = ((~` a `=>` ~` b) `&&` ~` b).
Proof. OM_autodec a b. Qed.

(* Sasaki implication and Sasaki conjunction including two variables *)

Lemma shookxJxy a b : a `=>` (a `&&` b) = ~` a `|` b.
Proof. OM_autodec a b. Qed.

Lemma shookxJOxy a b : a `=>` (~` a `&&` b) = ~` a.
Proof. OM_autodec a b. Qed.

Lemma shookxJyx a b : a `=>` (b `&&` a) = (a `=>` b).
Proof. OM_autodec a b. Qed.

Lemma shookxJyOx a b : a `=>` (b `&&` ~` a) = ~` a.
Proof. OM_autodec a b. Qed.

Lemma sprojxHxy a b : a `&&` (a `=>` b) = a `&` b.
Proof. OM_autodec a b. Qed.

Lemma sprojxHOxy a b : a `&&` (~` a `=>` b) = a.
Proof. OM_autodec a b. Qed.

Lemma sprojxHyx a b : a `&&` (b `=>` a) = a.
Proof. OM_autodec a b. Qed.

Lemma sprojxHyOx a b : a `&&` (b `=>` ~` a) = (a `&&` ~` b).
Proof. OM_autodec a b. Qed.

Lemma shookJxyx a b : (a `&&` b) `=>` a = \top.
Proof. OM_autodec a b. Qed.

Lemma shookJxyOx a b : (a `&&` b) `=>` ~` a = (a `=>` ~` b).
Proof. OM_autodec a b. Qed.

Lemma shookJxyy a b : (a `&&` b) `=>` b = (a `=>` (b `=>` a)).
Proof. OM_autodec a b. Qed.

Lemma shookJxyOy a b : (a `&&` b) `=>` ~` b = (a `=>` ~` b).
Proof. OM_autodec a b. Qed.

Lemma sprojHxyx a b : (a `=>` b) `&&` a = a `&` b.
Proof. OM_autodec a b. Qed.

Lemma sprojHxyOx a b : (a `=>` b) `&&` ~` a = ~` a.
Proof. OM_autodec a b. Qed.

Lemma sprojHxyy a b : (a `=>` b) `&&` b = ((~` a `=>` ~` b) `=>` b).
Proof. OM_autodec a b. Qed.

Lemma sprojHxyOy a b : (a `=>` b) `&&` ~` b = (~` a `&&` ~` b).
Proof. OM_autodec a b. Qed.

End OModularLatticeF2Theory.

Module Import DualOModularLattice.
Section DualOModularLattice.
Context {disp : unit} {L : oModularLatticeType disp}.

Lemma dual_le_joinIO : orthomodular_law L^d.
Proof.
move=>a b; rewrite /ocompl/= /le/= /join/= {2}/meet/= -leO
  =>/le_joinIO/(f_equal ocompl).
by rewrite ocomplU ocomplI !ocomplK.
Qed.

HB.instance Definition _ :=
  hasOrthoModular.Build (dual_display disp) L^d dual_le_joinIO.
End DualOModularLattice.
End DualOModularLattice.

Section ModularLatticeTheory.
Variable (disp : unit) (T : modularLatticeType disp).
Implicit Type (x y z : T).

End ModularLatticeTheory.

Module Import DualModularLattice.
Section DualModularLattice.
Context {disp : unit} {L : modularLatticeType disp}.

Lemma dual_le_joinI : modular_law L^d.
Proof.
move=>a b c; rewrite /ocompl/= /le/= /join/= {2 3}/meet/= -leO=>/le_joinI=>P.
move: (P (~` b))=>/(f_equal ocompl); rewrite {3 7}/ocompl/=.
by rewrite !ocomplU !ocomplI ocomplU !ocomplK.
Qed.

HB.instance Definition _ :=
  hasModular.Build (dual_display disp) L^d dual_le_joinI.
End DualModularLattice.
End DualModularLattice.

(* on latticeType, build complLattice orthoLattice *)
HB.factory Record TBLattice_isOrthoLattice (d : unit) T of TBLattice d T := {
  ocompl : T -> T;
  joinOx : forall a, join (ocompl a) a = top;
  meetOx : forall a, meet (ocompl a) a = bottom;
  ocomplK  : involutive ocompl;
  leOP : {homo ocompl : a b /~ a <= b};
}.
HB.builders Context d T of TBLattice_isOrthoLattice d T.
HB.instance Definition _ := @has_ocompl.Build d T ocompl joinOx meetOx.
HB.instance Definition _ := @ComplLattice_isOrthoLattice.Build d T ocomplK leOP.
HB.end.

(* build on orthocompl, since modular law is stronger than orthomodular law *)
HB.factory Record OrthoLattice_isModularLattice (d : unit) T of OrthoLattice d T := {
  le_joinI : forall a b c : T, a <= c -> join a (meet b c) = meet (join a b) c;
}.
HB.builders Context d T of OrthoLattice_isModularLattice d T.
HB.instance Definition _ := @hasOrthoModular.Build d T (modular_is_orthomodular le_joinI).
HB.instance Definition _ := @hasModular.Build d T le_joinI.
HB.end.

HB.factory Record TBLattice_isModularLattice (d : unit) T of TBLattice d T := {
  ocompl : T -> T;
  joinOx : forall a, join (ocompl a) a = top;
  meetOx : forall a, meet (ocompl a) a = bottom;
  ocomplK  : involutive ocompl;
  leO : {homo ocompl : a b /~ a <= b};
  le_joinI : forall a b c : T, a <= c -> join a (meet b c) = meet (join a b) c;
}.
HB.builders Context d T of TBLattice_isModularLattice d T.
HB.instance Definition _ := @TBLattice_isOrthoLattice.Build d T
  ocompl joinOx meetOx ocomplK leO.
HB.instance Definition _ := @OrthoLattice_isModularLattice.Build d T le_joinI.
HB.end.

HB.factory Record POrder_isOrtholattice d T of POrder d T := {
  t : T;
  meet : T -> T -> T;
  join : T -> T -> T;
  compl : T -> T;
  joinKI : forall b a, meet a (join a b) = a;
  joinCICx : forall a b c,
    join (join a b) c = join (compl (meet (compl c) (compl b))) a;
  joinxIC : forall a b, a = join a (meet b (compl b));
  leEmeet : forall a b, (a <= b) = (meet a b == a);
}.
HB.builders Context d T of POrder_isOrtholattice d T.

Implicit Type (a b c : T).

Local Notation "~` x" := (compl x).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).

Let bot := t `&` ~` t.
Let top := ~` bot.

Fact P0 a : a `|` bot = a.
Proof. by rewrite -joinxIC. Qed.

Fact P1 a : a `&` a = a.
Proof. by rewrite {2}(joinxIC a t) joinKI. Qed.

Fact P2 : ~` ~` bot = bot.
Proof. by move: (joinCICx bot bot bot); rewrite !P0 P1. Qed.

Fact P3 a : bot `|` a = a.
Proof. by move: (joinCICx a bot bot); rewrite !P0 P1 P2. Qed.

Fact P4 a : a `&` ~` a = bot.
Proof. by rewrite -[LHS]P3 {1}/bot -joinxIC. Qed.

Fact P5 b c : b `|` c = ~` (~` c `&` ~` b).
Proof. by move: (joinCICx bot b c); rewrite P3 P0. Qed.

Fact P6 b : b `|` b = ~` ~` b.
Proof. by rewrite P5 P1. Qed.

Fact joinC : commutative join.
Proof. by move=>a b; move: (joinCICx a b bot); rewrite P0 -P5 P0. Qed.

Fact joinA : associative join.
Proof.
by move=>a b c; move: (joinCICx a b c); rewrite [_ `|` a]joinC -P5.
Qed.

Fact ocomplK : involutive compl.
Proof. 
by move=>a; move: (joinKI a (~` a))=>/(f_equal compl);
rewrite [~` a `|` a]P5 P4 -P5 P3.
Qed.

Fact P10 b c : ~` (b `|` c) = ~` b `&` ~` c.
Proof. by rewrite joinC P5 ocomplK. Qed.

Fact P11 b c : ~` (b `&` c) = ~` b `|` ~` c.
Proof. by rewrite joinC P5 !ocomplK. Qed.

Fact meetC : commutative meet.
Proof. by move=>a b; rewrite -[LHS]ocomplK P11 joinC -P11 ocomplK. Qed.

Fact meetA : associative meet.
Proof. by move=>a b c; rewrite -[LHS]ocomplK P11 P11 joinA -P11 -P11 ocomplK. Qed.

Fact meetKU : forall b a, a `|` (a `&` b) = a.
Proof.
by move=>b a; rewrite -[LHS]ocomplK P10 [~` (a `&` b)]P11 joinKI ocomplK.
Qed.

Fact meetOx : forall a, (~` a) `&` a = bot.
Proof. by move=>a; rewrite meetC P4. Qed.

Fact joinOx : forall a, (~` a) `|`  a = top.
Proof. by move=>a; rewrite /top -(meetOx a) P11 ocomplK joinC. Qed.

Fact leOP : {homo compl : a b /~ a <= b}.
Proof.
move=>a b; rewrite !leEmeet=>/eqP/(f_equal compl)<-.
by rewrite P11 joinC joinKI.
Qed.

Fact le0x : forall a, bot <= a.
Proof. by move=>a; rewrite leEmeet -[a]P3 joinKI. Qed.

Fact lex1 : forall a, a <= top.
Proof. by move=>a; rewrite leEmeet -(joinOx (~` a)) ocomplK joinKI. Qed.

HB.instance Definition _ := POrder_isLattice.Build d T 
  meetC joinC meetA joinA joinKI meetKU leEmeet.
HB.instance Definition _ := hasBottom.Build d T le0x.
HB.instance Definition _ := hasTop.Build d T lex1.
HB.instance Definition _ := has_ocompl.Build d T joinOx meetOx.
HB.instance Definition _ := ComplLattice_isOrthoLattice.Build d T ocomplK leOP.
HB.end.

(* HB.factory Record POrder_isOrtholattice *)