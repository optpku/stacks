/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.Hom Scheme.Modules
open Scheme.DerivedQCoh
open ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The Euler characteristic of proper derived global cohomology over a field. -/
noncomputable def derivedEulerCharacteristic
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (K : DerivedQCoh X) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℤ) (fun i ↦ cohomologyOverField f K i)

/-- The derived Euler characteristic is the signed finite sum of the dimensions of proper
derived global cohomology. -/
theorem derivedEulerCharacteristic_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (K : DerivedQCoh X) :
    derivedEulerCharacteristic f K =
      ∑ᶠ i : ℤ, (Int.negOnePow i : ℤ) * Module.finrank k (cohomologyOverField f K i) := sorry

/-- Isomorphic derived quasicoherent objects have equal proper derived Euler
characteristics. -/
theorem derivedEulerCharacteristic_eq_of_iso
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    {K L : DerivedQCoh X} (e : K ≅ L) :
    derivedEulerCharacteristic f K = derivedEulerCharacteristic f L := sorry

/-- For a proper scheme over a field of Krull dimension at most one, the structure-sheaf
Euler characteristic equals that of the proper dualizing complex. -/
theorem structureSheafEulerCharacteristic_eq
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    let _ : (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules).IsCoherent :=
      @structureSheaf_isCoherent X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
    eulerCharacteristic X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) =
      derivedEulerCharacteristic X.hom (properDualizingComplex X.hom) := sorry

/-- For a proper Cohen–Macaulay equidimensional scheme of Krull dimension one, the
structure-sheaf Euler characteristic is the negative of the curve dualizing-module Euler
characteristic. -/
theorem structureSheafEulerCharacteristic_eq_neg_curveModule
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.CohenMacaulay X.left] [EquidimensionalSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1) :
    let _ : (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules).IsCoherent :=
      @structureSheaf_isCoherent X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
    let _ : (curveDualizingModule X.hom).IsCoherent :=
      curveDualizingModule_isCoherent X h_dimension.le
    eulerCharacteristic X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) =
      -eulerCharacteristic X.hom (curveDualizingModule X.hom) := sorry

end AlgebraicGeometry.Scheme.Hom
