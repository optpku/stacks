/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison

/-!
# Comparison for derived quasi-coherent modules on algebraic spaces

The weak-Serre inclusion `QCoh X ⥤ Modules X` induces the canonical unbounded
comparison `DerivedCategory (QCoh X) ⥤ DerivedQCoh X`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- The standard derived-category structure on quasi-coherent modules on an algebraic
space. -/
instance hasDerivedCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasDerivedCategory (QCoh X) :=
  HasDerivedCategory.standard (QCoh X)

end AlgebraicGeometry.AlgebraicSpace.QCoh

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The canonical comparison from the derived category of quasi-coherent modules to
derived modules with quasi-coherent cohomology. -/
noncomputable abbrev comparison {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedCategory (QCoh X) ⥤ DerivedQCoh X :=
  DerivedCategory.CohomologyIn.Comparison.functor (quasiCoherentModuleProperty X)

namespace comparison

/-- Forgetting the comparison recovers the derived functor of the quasi-coherent
inclusion. -/
noncomputable def compInclusionIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    comparison X ⋙ inclusion X ≅ (QCoh.inclusion X).mapDerivedCategory :=
  DerivedCategory.CohomologyIn.Comparison.compιIso (quasiCoherentModuleProperty X)

end comparison

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
