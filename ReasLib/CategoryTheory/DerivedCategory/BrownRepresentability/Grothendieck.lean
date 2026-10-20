/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Brown Representability for Grothendieck Derived Categories

The unbounded derived category of a Grothendieck abelian category need not be compactly
generated.  Its Brown-representability theorem is instead exposed through a detecting
factorization set, which is the abstraction consumed by the general Brown API.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe w v u v' u'

namespace CategoryTheory.DerivedCategory.Brown

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{max (max u v) w} A]

/-- A Grothendieck abelian category admits a Brown-representability set in its unbounded
derived category.  This is the reusable replacement for the generally false assertion that
the derived category is compactly generated. -/
@[stacks 0F5X "Brown-representability set"]
theorem existsSet :
    ∃ S : _root_.Set (DerivedCategory A), BrownRepresentability.IsSet S := sorry

/-- Lemma 19.15.1: every contravariant homological functor on the derived category of a
Grothendieck abelian category that sends coproducts to products is representable. -/
@[stacks 0F5X]
theorem existsRepresentation
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{w})
    (hH : H.rightOp.IsHomological)
    [hprod : ∀ J : Type (max (max u v) w), PreservesLimitsOfShape (Discrete J) H] :
    ∃ X : DerivedCategory A, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

end CategoryTheory.DerivedCategory.Brown

namespace CategoryTheory.Functor.Brown.Grothendieck

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{max (max u v) w} A]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [_root_.CategoryTheory.IsTriangulated D]

/-- An exact coproduct-preserving functor from a Grothendieck derived category is a left
adjoint.  The hypothesis is routed through the Brown set rather than compact generation. -/
@[stacks 0F5Y "left-adjoint form"]
theorem isLeftAdjoint
    (F : DerivedCategory A ⥤ D) [LocallySmall.{w} D]
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max (max u v) w), PreservesColimitsOfShape (Discrete J) F] :
    F.IsLeftAdjoint := sorry

/-- Proposition 19.15.2: an exact coproduct-preserving functor from a Grothendieck derived
category admits a right adjoint with a triangulated structure. -/
@[stacks 0F5Y]
theorem hasTriangulatedRightAdjoint
    (F : DerivedCategory A ⥤ D) [LocallySmall.{w} D]
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max (max u v) w), PreservesColimitsOfShape (Discrete J) F] :
    ∃ (G : D ⥤ DerivedCategory A) (adj : F ⊣ G),
      G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ) := sorry

end CategoryTheory.Functor.Brown.Grothendieck
