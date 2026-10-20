/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

/-!
# Eta complexes for ideal sheaves on schemes

This file establishes quasicoherence of eta complexes associated to effective
Cartier ideal sheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.Eta

variable {X : Scheme.{u}}

/-- Every term of the ideal-sheaf eta complex of a termwise quasicoherent,
action-monic complex is quasicoherent. -/
instance termIsQuasicoherent (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K] (i : ℤ) :
    ((RingedSpace.IdealSheaf.Eta.complex D.toSubobject K).X i).IsQuasicoherent := sorry

/-- The ideal-sheaf eta complex of a termwise quasicoherent, action-monic complex
is termwise quasicoherent. -/
theorem termsInQuasiCoherent (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K] :
    CochainComplex.termsIn (Scheme.quasiCoherentModuleProperty X)
      (RingedSpace.IdealSheaf.Eta.complex D.toSubobject K) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData.Eta
