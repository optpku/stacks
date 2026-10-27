/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
public import ReasLib.Algebra.Module.IdealPower.Serre

@[expose] public section

open CategoryTheory
open DerivedCategory.CohomologyIn.Comparison

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTorsion

/-- For finitely generated `I`, the derived inclusion is bijective on morphisms between
degree-zero objects of ideal-power-torsion modules. -/
theorem derivedInclusion_hom_bijective
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : ModuleCat.IdealPowerTorsion.category I) :
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj M ⟶
        (DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj N ↦
      (ModuleCat.IdealPowerTorsion.derivedInclusion I).map f) := sorry

/-- For finitely generated `I`, the derived inclusion is bijective on degree-one `ShiftedHom`
between ideal-power-torsion modules. -/
theorem derivedInclusion_extOne_bijective
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : ModuleCat.IdealPowerTorsion.category I) :
    Function.Bijective (fun e : ShiftedHom
      ((DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj N) (1 : ℤ) ↦
      e.map (ModuleCat.IdealPowerTorsion.derivedInclusion I)) := sorry

/-- There exist a finitely generated ideal and ideal-power-torsion modules for which the
degree-two `ShiftedHom` map induced by the derived inclusion is not surjective. -/
theorem exists_derivedInclusion_extTwo_not_surjective :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A) (hI : I.FG)
      (M N : ModuleCat.IdealPowerTorsion.category I),
      ¬ Function.Surjective (fun e : ShiftedHom
        ((DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj N) (2 : ℤ) ↦
        e.map (ModuleCat.IdealPowerTorsion.derivedInclusion I)) := sorry

/-- There exist a finitely generated ideal for which the canonical comparison from the derived
category of ideal-power-torsion modules is not an equivalence. -/
theorem exists_comparison_not_equivalence :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A) (hI : I.FG),
      letI : Fact I.FG := ⟨hI⟩
      ¬ (functor
        (ModuleCat.isIdealPowerTorsion I : ObjectProperty (ModuleCat.{u} A))).IsEquivalence := sorry

end CategoryTheory.ModuleCat.IdealPowerTorsion

end
