/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.KInjective.Category
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Resolution

/-!
# K-injective resolutions and the DG derived category

Functorial K-injective resolutions make the canonical functor from K-injective homotopy objects
to the DG derived category essentially surjective, hence an equivalence.
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
-- sheaf/free elaboration.  Both sides of the K-injective equivalence must share this choice.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.KInjective.toDerived

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A functorial K-injective resolution makes every DG derived object isomorphic to the image
of a K-injective homotopy object. -/
theorem essSurj_of_resolution {𝒜 : DGA(𝒪)}
    (R : Module.KInjective.ResolutionFunctor 𝒜) :
    (Homotopy.KInjective.toDerived 𝒜).EssSurj := sorry

/-- Every DG derived object has a K-injective homotopy representative. -/
instance essSurj (𝒜 : DGA(𝒪)) :
    (Homotopy.KInjective.toDerived 𝒜).EssSurj := sorry

/-- A functorial K-injective resolution makes the canonical K-injective model equivalent to
the DG derived category. -/
theorem isEquivalence_of_resolution {𝒜 : DGA(𝒪)}
    (R : Module.KInjective.ResolutionFunctor 𝒜) :
    Functor.IsEquivalence (Homotopy.KInjective.toDerived 𝒜) := sorry

/-- The canonical K-injective model is equivalent to the DG derived category. -/
instance isEquivalence (𝒜 : DGA(𝒪)) :
    Functor.IsEquivalence (Homotopy.KInjective.toDerived 𝒜) := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.KInjective.toDerived
