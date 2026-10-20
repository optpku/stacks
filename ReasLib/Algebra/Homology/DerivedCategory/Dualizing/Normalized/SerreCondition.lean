module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.DualizingModule
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
variable (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)

/-- The dualizing module of a normalized dualizing complex satisfies Serre's
condition `(S₂)`. -/
theorem dualizingModuleSerreConditionSTwo :
    Module.SerreConditionS A (dualizingModule H ω hω) 2 := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

end
