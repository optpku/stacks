/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.DerivedCompletion

@[expose] public section

open CategoryTheory
open DerivedCategory
open DerivedCategory.DerivedComplete
open DerivedCategory.DerivedCompletion

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.TorsionComplete

variable {A : Type u} [CommRing A]

/-- Derived `I`-adic completion restricted from objects with `I`-power-torsion
cohomology to derived-complete objects. -/
noncomputable def completion (I : Ideal A) (hI : I.FG) :
    IdealPowerTorsion I ⥤ category I :=
  IdealPowerTorsion.inclusion I ⋙
    (chosenReflector I hI).toFullSubcategory

/-- Closed-support local cohomology restricted from derived-complete objects to
objects with `I`-power-torsion cohomology. -/
noncomputable def localCohomology (I : Ideal A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I) :
    category I ⥤ IdealPowerTorsion I :=
  (derivedCompleteObjectProperty I).ι ⋙ RΓZ

/-- The adjunction between restricted derived completion and restricted
closed-support local cohomology. -/
noncomputable def adjunction (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    completion I hI ⊣ localCohomology I RΓZ :=
  hRΓZ.comp (chosenReflector_spec I hI)

/-- The unit of the restricted completion-local-cohomology adjunction is
pointwise invertible. -/
noncomputable instance unitAppIsIso (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : IdealPowerTorsion I) :
    IsIso ((adjunction I hI RΓZ hRΓZ).unit.app K) := sorry

/-- The counit of the restricted completion-local-cohomology adjunction is
pointwise invertible. -/
noncomputable instance counitAppIsIso (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (L : category I) :
    IsIso ((adjunction I hI RΓZ hRΓZ).counit.app L) := sorry

/-- For a finitely generated ideal `I`, derived completion and closed-support
local cohomology restrict to quasi-inverse equivalences between derived objects
with `I`-power-torsion cohomology and derived-complete objects. -/
noncomputable def equivalence (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    IdealPowerTorsion I ≌ category I :=
  (adjunction I hI RΓZ hRΓZ).toEquivalence

/-- The forward functor of the completion-local-cohomology equivalence is
restricted derived completion. -/
theorem equivalence_functor (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    (equivalence I hI RΓZ hRΓZ).functor = completion I hI := sorry

/-- The inverse functor of the completion-local-cohomology equivalence is
restricted local cohomology. -/
theorem equivalence_inverse (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    (equivalence I hI RΓZ hRΓZ).inverse = localCohomology I RΓZ := sorry

end CategoryTheory.DerivedCategory.TorsionComplete
