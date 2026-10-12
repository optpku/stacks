/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeEmbedding

/-!
# Pushouts along thickenings and affine morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme pushout along a thickening and an affine morphism remains a pushout after embedding
schemes over the base into algebraic spaces. -/
theorem isPushout_ofOver_thickening_affine {S : Scheme.{u}} {X X' Y Y' : Over S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    [AlgebraicGeometry.IsThickening i.left] [IsAffineHom f.left]
    (h : IsPushout i.left f.left i'.left g.left) :
    IsPushout ((schemeFunctor S).map i) ((schemeFunctor S).map f)
      ((schemeFunctor S).map i') ((schemeFunctor S).map g) := sorry

end AlgebraicGeometry.AlgebraicSpace
