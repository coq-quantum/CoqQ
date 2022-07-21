(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Section ExtraVector.
Context {K : fieldType} {E : vectType K}.

Lemma spanZ (x : K) (u : E) : x != 0 -> (<[x *: u]> = <[u]>)%VS.
Proof.
move=> nz_x; rewrite (rwP eqP) eqEsubv; apply/andP; split.
- apply/subvP => v /vlineP[/= k ->]; apply/vlineP.
  by exists (k * x); rewrite scalerA.
- apply/subvP => v /vlineP[/= k ->]; apply/vlineP.
  by exists (k / x); rewrite scalerA mulfVK.
Qed.

Lemma size_vbasis (U : {vspace E}) : size (vbasis U) = \dim U.
Proof.
have /[dup] := vbasisP U; rewrite {1}basisEfree => /and3P[_ _ dimle].
rewrite basisEdim => /andP[_ dimge]; apply/eqP.
by rewrite eq_le !leEnat !(dimle, dimge).
Qed.
End ExtraVector.
