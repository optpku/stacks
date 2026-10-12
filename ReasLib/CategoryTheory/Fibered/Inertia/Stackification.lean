/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.LocalEquivalence
import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Basic.Objects
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Criteria
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inertia and stackification

The heterogeneous local-equivalence closure of absolute inertia upgrades to a stackification.
Stackness of the target inertia follows from stackness of the original target and the neutral
inertia closure; the fixed-universe theorem is retained as a bicategorical specialization.
-/

@[expose] public section

universe u v w vS uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor.Inertia.map

variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered] [p₂.IsFibered]

/-- Absolute inertia sends a heterogeneous stackification to a heterogeneous
stackification. -/
@[stacks 06NS "heterogeneous inertia preserves stackifications"]
theorem isStackification
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : CartesianBasedFunctor.IsStackification J F) :
    CartesianBasedFunctor.IsStackification J
      (CartesianBasedFunctor.Inertia.map F) := sorry

end CartesianBasedFunctor.Inertia.map

namespace FiberedCategoryOver.Inertia

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

namespace map

/-- Absolute inertia sends a stackification comparison to a stackification comparison. -/
@[stacks 06NS "fixed-universe inertia preserves stackifications"]
theorem isStackification
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : FiberedCategoryOver.Hom.IsStackification J F) :
    FiberedCategoryOver.Hom.IsStackification J (map F) := sorry

end map

end FiberedCategoryOver.Inertia

end CategoryTheory
