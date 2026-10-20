/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.KInjective

/-!
# The K-injective model of the DG derived category

The canonical localization is fully faithful on the full subcategory of K-injective DG
homotopy objects.  This file packages that fact as a functor so downstream code can work with
the K-injective model without repeatedly unfolding the localization map on morphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  The K-injective subcategory inherits the pinned homotopy structure.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.KInjective

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The canonical functor from K-injective DG homotopy objects to the DG derived category. -/
def toDerived (𝒜 : DGA(𝒪)) :
    Homotopy.KInjective 𝒜 ⥤ DerivedCategory 𝒜 :=
  Homotopy.KInjective.ι 𝒜 ⋙ DerivedCategory.Qh 𝒜

namespace toDerived

/-- Passage to the derived category is bijective on morphisms between K-injective DG
homotopy objects. -/
theorem map_bijective (𝒜 : DGA(𝒪))
    (I I' : Homotopy.KInjective 𝒜) :
    Function.Bijective
      ((KInjective.toDerived 𝒜).map : (I ⟶ I') → _) := sorry

/-- The canonical functor from K-injective DG homotopy objects is full. -/
instance full (𝒜 : DGA(𝒪)) :
    (KInjective.toDerived 𝒜).Full := sorry

/-- The canonical functor from K-injective DG homotopy objects is faithful. -/
instance faithful (𝒜 : DGA(𝒪)) :
    (KInjective.toDerived 𝒜).Faithful := sorry

end toDerived

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.KInjective
