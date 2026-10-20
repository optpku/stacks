/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- If `p : X ⟶ S` is quasi-compact and quasi-separated, then the derived pushforward of
the relative de Rham complex has quasicoherent cohomology on `S`. -/
theorem pushforwardDerivedComplex_isQuasicoherent {X S : Scheme.{u}} (p : X ⟶ S)
    [QuasiCompact p] [QuasiSeparated p] :
    Scheme.derivedQuasiCoherentModuleProperty S
      ((RingedSpace.moduleDerivedPushforward
        (ModuleCech.relativeSpaceMap p.toLRSHom.toShHom)).obj
        ((CochainComplex.Nat.toDerived
          (ModuleCech.relativeSpace p.toLRSHom.toShHom).Modules).obj
          (RingedSpace.DeRham.complex p.toLRSHom.toShHom))) := sorry

/-- If `p : X ⟶ S` is proper and `S` is locally Noetherian, then the derived pushforward of
the relative de Rham complex has coherent cohomology on `S`. -/
theorem pushforwardDerivedComplex_isCoherent {X S : Scheme.{u}} (p : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper p] :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent S.toRingedSpace.ringCatSheaf)
      ((RingedSpace.moduleDerivedPushforward
        (ModuleCech.relativeSpaceMap p.toLRSHom.toShHom)).obj
        ((CochainComplex.Nat.toDerived
          (ModuleCech.relativeSpace p.toLRSHom.toShHom).Modules).obj
          (RingedSpace.DeRham.complex p.toLRSHom.toShHom))) := sorry

end AlgebraicGeometry.Scheme.DeRham
