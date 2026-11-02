/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.MinimalFreeModel
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Derived-fiber Euler characteristic on algebraic spaces

The Euler characteristic of a derived `𝒪_X`-module at a point of an algebraic space is
computed from residue-field homology of the derived étale stalk at a geometric point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Degree-`i` residue-field homology of the derived étale stalk of `E` at a geometric
point. -/
noncomputable def fiberHomology (E : ModuleDerived X) (xbar : GeometricPoint X) (i : ℤ) :
    ModuleCat (IsLocalRing.ResidueField (etaleLocalRing X xbar)) :=
  CategoryTheory.DerivedCategory.ResidueField.homology (etaleLocalRing X xbar)
    (stalkDerived xbar E) i

/-- The degree-`i` Betti number of `E` at a geometric point. -/
noncomputable def fiberBettiAt (E : ModuleDerived X) (xbar : GeometricPoint X) (i : ℤ) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField (etaleLocalRing X xbar))
    (fiberHomology E xbar i)

/-- The Euler characteristic of the derived residue-field fiber of `E` at a geometric
point. -/
noncomputable def fiberEulerCharAt (E : ModuleDerived X) (xbar : GeometricPoint X) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℤ) (fun i ↦ fiberHomology E xbar i)

/-- The degree-`i` Betti number `β_i(x)` of `E` at a point of `X`. -/
noncomputable def fiberBetti (E : ModuleDerived X) (i : ℤ) (x : Points X) : ℕ :=
  fiberBettiAt E (AlgebraicGeometry.AlgebraicSpace.geometricPointOver x) i

/-- The Euler characteristic `χ_E(x)` of the derived residue-field fiber of `E` at a point
of `X`. -/
noncomputable def fiberEulerChar (E : ModuleDerived X) (x : Points X) : ℤ :=
  fiberEulerCharAt E (AlgebraicGeometry.AlgebraicSpace.geometricPointOver x)

/-- The fiber Betti number is the finrank of residue-field homology at the chosen geometric
point over `x`. -/
theorem fiberBetti_apply (E : ModuleDerived X) (i : ℤ) (x : Points X) :
    fiberBetti E i x =
      Module.finrank
        (IsLocalRing.ResidueField
          (etaleLocalRing X (AlgebraicGeometry.AlgebraicSpace.geometricPointOver x)))
        (fiberHomology E (AlgebraicGeometry.AlgebraicSpace.geometricPointOver x) i) :=
  rfl

/-- The derived-fiber Euler characteristic is the finsum of signed Betti numbers. -/
theorem fiberEulerChar_apply (E : ModuleDerived X) (x : Points X) :
    fiberEulerChar E x =
      ∑ᶠ i : ℤ, (Int.negOnePow i : ℤ) * fiberBetti E i x :=
  rfl

/-- The Euler characteristic at the image of a geometric point agrees with the value at
that geometric point. -/
theorem fiberEulerChar_spec (E : ModuleDerived X) (xbar : GeometricPoint X) :
    fiberEulerChar E xbar.image = fiberEulerCharAt E xbar := sorry

/-- Isomorphic derived modules have the same derived-fiber Euler-characteristic function. -/
theorem fiberEulerChar_eq_of_iso {E F : ModuleDerived X} (e : E ≅ F) :
    fiberEulerChar E = fiberEulerChar F := by
  funext x
  rw [fiberEulerChar_apply, fiberEulerChar_apply]
  apply finsum_congr
  intro i
  have hi : fiberBetti E i x = fiberBetti F i x := by
    let xbar := AlgebraicGeometry.AlgebraicSpace.geometricPointOver x
    let R := etaleLocalRing X xbar
    let eStalk :=
      ((GeometricPoint.toSmallEtalePoint xbar).sheafModuleStalkFunctor
        (structureSheaf X)).mapDerivedCategory.mapIso e
    let eFiber :=
      (ModuleCat.derivedExtensionOfScalars
        (algebraMap R (IsLocalRing.ResidueField R))).mapIso eStalk
    exact ((DerivedCategory.homologyFunctor
      (ModuleCat (IsLocalRing.ResidueField R)) i).mapIso eFiber).toLinearEquiv.finrank_eq
  rw [hi]

/-- Perfect derived modules have finite-dimensional residue-field fiber cohomology in every
degree. -/
theorem fiberCohomology_finiteDimensional (E : ModuleDerived X) (hE : IsPerfect E)
    (xbar : GeometricPoint X) (i : ℤ) :
    FiniteDimensional (IsLocalRing.ResidueField (etaleLocalRing X xbar))
      (fiberHomology E xbar i) := sorry

/-- Perfect derived modules have residue-field fiber cohomology supported in only finitely
many degrees. -/
theorem fiberCohomology_finiteSupport (E : ModuleDerived X) (hE : IsPerfect E)
    (xbar : GeometricPoint X) :
    Set.Finite (setOf fun i : ℤ ↦ ¬ IsZero (fiberHomology E xbar i)) := sorry

/-- The Euler characteristic of the derived residue-field fibers of a perfect derived
module on an algebraic space is locally constant on `Points X`. -/
theorem fiberEulerChar_isLocallyConstant (E : ModuleDerived X) (hE : IsPerfect E) :
    IsLocallyConstant (fiberEulerChar E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
