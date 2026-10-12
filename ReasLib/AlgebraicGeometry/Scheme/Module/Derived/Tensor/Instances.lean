/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.DerivedCategory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula

/-- Complexes of modules on a scheme admit K-flat resolutions. -/
theorem hasKFlatResolutions (X : Scheme.{u}) :
    HomotopyCategory.KFlat.HasResolutions X.Modules :=
  RingedSpace.ModuleDerived.modulesHasKFlatResolutions X.toRingedSpace

/-- The tensor bifunctor on scheme modules admits a canonical total left-derived model. -/
theorem hasDerivedTensorBifunctor (X : Scheme.{u}) :
    DerivedTensor.Bifunctor.Has
      (C := RingedSpace.Modules X.toRingedSpace) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula
