/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Families of curves over an algebraic space

Families of curves equipped with a morphism from their base scheme to an
algebraic space form a category fibred in groupoids over schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.CurvesGroupoidsOver

/-- The projection sending a family of curves equipped with a map from its base
scheme to `B` to its base scheme over `S`. -/
def p {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CostructuredArrow (Curves.p S ⋙ ofOverFunctor S) B ⥤ Over S :=
  CostructuredArrow.proj (Curves.p S ⋙ ofOverFunctor S) B ⋙ Curves.p S

/-- The projection to base schemes is the costructured-arrow projection
followed by the projection of families of curves. -/
theorem p_eq {S : Scheme.{u}} (B : AlgebraicSpace S) :
    p B = CostructuredArrow.proj (Curves.p S ⋙ ofOverFunctor S) B ⋙ Curves.p S := sorry

/-- The projection of families of curves with a map from their base scheme
to `B` is fibred in groupoids over `Over S`. -/
instance instIsFiberedInGroupoids {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Functor.IsFibered.InGroupoids (p B) := sorry

/-- Families of curves with a map from their base scheme to `B`, bundled as a
category fibred in groupoids over `Over S` at algebraic-space Hom-universe `u + 1`. -/
def toGroupoids {S : Scheme.{u}} (B : AlgebraicSpace S) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p B)

/-- The projection of the bundled category is the base-scheme projection. -/
theorem toGroupoids_p {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (toGroupoids B).p = p B := sorry

/-- The total category is the costructured-arrow category of families of curves
equipped with a map from their base scheme to `B`. -/
theorem toGroupoids_total {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (toGroupoids B).total = CostructuredArrow (Curves.p S ⋙ ofOverFunctor S) B := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.CurvesGroupoidsOver
