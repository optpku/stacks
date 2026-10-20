/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.InGroupoids
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Chosen

/-!
# Mapping stacks with scheme domain

The mapping category over a test scheme is the target groupoid over the product
of that test scheme with the domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The mapping stack from a scheme over `S` to a category fibred in groupoids over `S`,
constructed by categorical pullback along the product functor. -/
def homStack (X : Over S) (Z : GroupoidsOver S) : GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.ofFunctor
    (CategoricalPullback.π₁ (tensorLeft X) Z.p)

/-- The mapping-stack projection is the first projection of the categorical pullback
along the product functor. -/
theorem homStack_p (X : Over S) (Z : GroupoidsOver S) :
    (homStack X Z).p = CategoricalPullback.π₁ (tensorLeft X) Z.p := rfl

/-- The fibre of the mapping stack over `T` is equivalent to the target fibre over `X ×_S T`. -/
def homStack_fiberEquivalence (X : Over S) (Z : GroupoidsOver S) (T : Over S) :
    (homStack X Z).p.Fiber T ≌ Z.p.Fiber (X ⊗ T) :=
  CategoricalPullback.Fiber.chosen.equivalence (tensorLeft X) Z.p T

end AlgebraicGeometry.GroupoidsOver
