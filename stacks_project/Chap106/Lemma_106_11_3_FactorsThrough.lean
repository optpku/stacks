/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Factorization

/-!
# Valuative squares with factored generic arrows

The factored-square structure, its constructor, and its cone view are provided
by the shared valuative criterion API.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}
variable [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSqFactorsThrough :
  (U ⟶ X) → (X ⟶ Y) → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSqFactorsThrough.of :
  ∀ {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSq f)
    (genericToSource : GroupoidsOver.slice sq.specK ⟶ U),
    genericToSource ≫ h = sq.i₁ → ValuativeCommSqFactorsThrough h f)

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSqFactorsThrough.toCone :
  ∀ {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSqFactorsThrough h f),
    Bicategory.PseudoPullbackCone sq.sq.i₂ f)

end AlgebraicGeometry.AlgebraicStack
