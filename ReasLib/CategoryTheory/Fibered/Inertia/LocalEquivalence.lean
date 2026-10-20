/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fiberedness.Based

/-!
# Local equivalences and inertia

The absolute-inertia construction is already functorial on based categories. This module first
records heterogeneous local-equivalence closure for its cartesian map, then exposes the
fixed-universe bicategorical specialization.
-/

@[expose] public section

universe u v w vS uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor.Inertia.map

variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered] [p₂.IsFibered]

/-- Absolute inertia preserves heterogeneous local equivalences. -/
@[stacks 06NS "inertia preserves local equivalences"]
theorem isLocalEquivalence
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : CartesianBasedFunctor.IsLocalEquivalence J F) :
    CartesianBasedFunctor.IsLocalEquivalence J
      (CartesianBasedFunctor.Inertia.map F) := sorry

end CartesianBasedFunctor.Inertia.map

namespace FiberedCategoryOver.Inertia

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

namespace map

/-- The map on absolute inertia induced by a local equivalence of fibered categories is again a
local equivalence. -/
@[stacks 06NS "fixed-universe inertia preserves local equivalences"]
theorem isLocalEquivalence
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : FiberedCategoryOver.Hom.IsLocalEquivalence J F) :
    FiberedCategoryOver.Hom.IsLocalEquivalence J (map F) := sorry

end map

end FiberedCategoryOver.Inertia

end CategoryTheory
