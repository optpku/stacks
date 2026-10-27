/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Lifted
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient

/-!
# The lifted derived category of quasi-coherent modules
-/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty RingedSite.Hom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/-- The standard derived-category construction at the larger carrier universe. -/
instance liftedFppfModulesHasDerivedCategory :
    HasDerivedCategory.{u + 2} (LiftedFppfModules X) :=
  HasDerivedCategory.standard (LiftedFppfModules X)

/-- The ambient derived category at the same universe as `QC(X)`. -/
abbrev LiftedModuleDerived := DerivedCategory (LiftedFppfModules X)

/-- The cohomology-in subcategory for the genuine lifted `LQCoh^{fbc}` property. -/
abbrev LiftedDerivedLQCohFbc := DerivedCategory.CohomologyIn (liftedLqcohFbc X)

/-- Lifted `LQCoh^{fbc}` is a weak Serre class. -/
instance liftedLqcohFbc_isWeakSerreClass : IsWeakSerreClass (liftedLqcohFbc X) := sorry

/-- Cohomology in lifted `LQCoh^{fbc}` is a triangulated subcategory. -/
instance liftedDerivedLQCohFbc_isTriangulated :
    (DerivedCategory.cohomologyIn (liftedLqcohFbc X)).IsTriangulated :=
  inferInstance

/-- The inclusion of the cohomology-in subcategory into the ambient derived category. -/
abbrev LiftedDerivedLQCohFbc.inclusion :
    LiftedDerivedLQCohFbc X ⥤ LiftedModuleDerived X :=
  (DerivedCategory.cohomologyIn (liftedLqcohFbc X)).ι

/-- The actual parasitic cohomology subcategory of lifted `D_LQCoh^{fbc}`. -/
abbrev liftedDerivedParasitic : ObjectProperty (LiftedDerivedLQCohFbc X) :=
  (DerivedCategory.cohomologyIn (liftedParasiticModules X)).inverseImage
    (LiftedDerivedLQCohFbc.inclusion X)

/-- Parasitic cohomology in lifted `D_LQCoh^{fbc}` is triangulated. -/
instance liftedDerivedParasitic_isTriangulated :
    (liftedDerivedParasitic X).IsTriangulated := sorry

/-- The Verdier quotient of lifted locally quasi-coherent flat-base-change cohomology
by parasitic cohomology. -/
abbrev LiftedDerivedQCoh := ObjectProperty.verdierQuotient (liftedDerivedParasitic X)

/-- The canonical localization by parasitic cohomology. -/
abbrev LiftedDerivedQCoh.quotientFunctor :
    LiftedDerivedLQCohFbc X ⥤ LiftedDerivedQCoh X :=
  ObjectProperty.verdierQuotientFunctor (liftedDerivedParasitic X)

end AlgebraicGeometry.AlgebraicStack
