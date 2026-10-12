/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeEmbedding
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.StructureMap

/-!
# Pushouts of admissible spans in algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open Scheme.Pushout Scheme.Pushout.IsAdmissibleSpan

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An admissible scheme pushout remains a pushout after applying the scheme embedding. -/
theorem isPushout_ofOver_admissibleSpan {S : Scheme.{u}} {Z X Y P : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
    [IsAdmissibleSpan i j]
    (h : IsPushout i.left j.left inl.left inr.left) :
    IsPushout ((schemeFunctor S).map i) ((schemeFunctor S).map j)
      ((schemeFunctor S).map inl) ((schemeFunctor S).map inr) := sorry

/-- The canonical algebraic-space pushout induced by the scheme-theoretic pushout is a pushout. -/
theorem isPushout_ofOver_admissibleSpan_toBase {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    IsPushout ((schemeFunctor S).map i) ((schemeFunctor S).map j)
      ((schemeFunctor S).map (Over.homMk (pushout.inl i.left j.left) (inl_toBase i j) :
        X ⟶ Over.mk (toBase i j)))
      ((schemeFunctor S).map (Over.homMk (pushout.inr i.left j.left) (inr_toBase i j) :
        Y ⟶ Over.mk (toBase i j))) := sorry

end AlgebraicGeometry.AlgebraicSpace
