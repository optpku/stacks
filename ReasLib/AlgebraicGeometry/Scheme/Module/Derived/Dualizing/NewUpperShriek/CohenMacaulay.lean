/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.LocallyShiftedSingle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.FlatQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- For a Cohen-Macaulay morphism, the new-upper-shriek dualizing object is locally
a coherent relative-flat module shifted by the locally constant fibre dimension. -/
theorem exists_dualizingModule_of_cohenMacaulay
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [AlgebraicGeometry.CohenMacaulay f.hom.left] :
    ∃ d : LocallyConstant X.obj.left ℕ, ∃ ω : (X.obj.left).Modules,
      (∀ x : X.obj.left, fiberDimensionAt f.hom.left x = (d x : WithBot ℕ∞)) ∧
      ω.IsCoherent ∧ SheafOfModules.IsFlatOver ω (f.hom.left).toShHom ∧
      IsLocallyShiftedSingle (D.dualizingObject f) ω d := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
