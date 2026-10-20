/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.MinimalFreeModel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X : Scheme.{u}}

/-- The Euler characteristic of the derived residue-field fiber of `E` at `x`. -/
noncomputable def fiberEulerChar
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (x : X) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℤ) (fun i ↦
    CategoryTheory.DerivedCategory.ResidueField.homology
      (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i)

/-- The derived-fiber Euler characteristic is the finsum of signed residue-field
cohomology dimensions. -/
theorem fiberEulerChar_apply
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (x : X) :
    fiberEulerChar E x = ∑ᶠ i : ℤ, (Int.negOnePow i : ℤ) *
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (CategoryTheory.DerivedCategory.ResidueField.homology
          (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i) := sorry

/-- Perfect derived modules have finite-dimensional residue-field fiber cohomology in
every degree. -/
theorem fiberCohomology_finiteDimensional
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (x : X) (i : ℤ) :
    FiniteDimensional (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (CategoryTheory.DerivedCategory.ResidueField.homology
        (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i) := sorry

/-- Perfect derived modules have residue-field fiber cohomology supported in only finitely
many degrees. -/
theorem fiberCohomology_finiteSupport
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (x : X) :
    Set.Finite {i : ℤ | ¬ CategoryTheory.Limits.IsZero
      (CategoryTheory.DerivedCategory.ResidueField.homology
        (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i)} := sorry

/-- Isomorphic derived modules have the same derived-fiber Euler-characteristic function. -/
theorem fiberEulerChar_eq_of_iso
    {E F : RingedSpace.ModuleDerived X.toRingedSpace} (e : E ≅ F) :
    fiberEulerChar E = fiberEulerChar F := sorry

/-- The Euler characteristic of the derived residue-field fibers of a perfect derived
module on a scheme is locally constant. -/
theorem fiberEulerChar_isLocallyConstant
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    IsLocallyConstant (fiberEulerChar E) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
