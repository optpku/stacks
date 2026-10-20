/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.DifferentialRescale
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Scalar.Multiplicity

/-!
# Multiplicity After Scaling One Differential

This file records finite-length consequences and multiplicity formulas for scaling one
differential of a two-periodic endomorphism.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]

/-- The zero/scalar complex on the range of an endomorphism has finite-length homology when
the scalar quotient of the ambient finite module has zero-dimensional support. -/
theorem rangeOfZeroScalar_homology_isFiniteLength
    [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : Module.End R M) (x : R)
    (hMx : Module.supportDim R (QuotSMulTop x M) ≤ 0) (i : ZMod 2) :
    IsFiniteLength R ((ofZeroScalar f.range x).toCochainComplex.homology i) := sorry

/-- Scaling the degree-zero differential preserves finite-length homology under the
zero-dimensional scalar-quotient hypothesis. -/
theorem smulD₀_homology_isFiniteLength
    [IsLocalRing R] [IsNoetherianRing R]
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (x : R) (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hMx : Module.supportDim R (QuotSMulTop x K.X) ≤ 0) (i : ZMod 2) :
    IsFiniteLength R ((smulD₀ K x).toCochainComplex.homology i) := sorry

/-- Scaling the degree-one differential preserves finite-length homology under the
zero-dimensional scalar-quotient hypothesis. -/
theorem smulD₁_homology_isFiniteLength
    [IsLocalRing R] [IsNoetherianRing R]
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (x : R) (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hMx : Module.supportDim R (QuotSMulTop x K.X) ≤ 0) (i : ZMod 2) :
    IsFiniteLength R ((smulD₁ K x).toCochainComplex.homology i) := sorry

/-- Scaling the degree-zero differential subtracts the multiplicity of the zero/scalar
complex on its range. -/
@[stacks 0EAC]
theorem multiplicity_smulD₀
    [IsLocalRing R] [IsNoetherianRing R]
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (x : R) (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hMx : Module.supportDim R (QuotSMulTop x K.X) ≤ 0) :
    (smulD₀ K x).multiplicity
        (smulD₀_homology_isFiniteLength K x h₀ h₁ hMx 0)
        (smulD₀_homology_isFiniteLength K x h₀ h₁ hMx 1) =
      K.multiplicity h₀ h₁ -
        (ofZeroScalar (LinearMap.range K.d₀.hom) x).multiplicity
          (rangeOfZeroScalar_homology_isFiniteLength K.d₀.hom x hMx 0)
          (rangeOfZeroScalar_homology_isFiniteLength K.d₀.hom x hMx 1) := sorry

/-- Scaling the degree-one differential adds the multiplicity of the zero/scalar complex
on its range. -/
@[stacks 0EAC]
theorem multiplicity_smulD₁
    [IsLocalRing R] [IsNoetherianRing R]
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (x : R) (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hMx : Module.supportDim R (QuotSMulTop x K.X) ≤ 0) :
    (smulD₁ K x).multiplicity
        (smulD₁_homology_isFiniteLength K x h₀ h₁ hMx 0)
        (smulD₁_homology_isFiniteLength K x h₀ h₁ hMx 1) =
      K.multiplicity h₀ h₁ +
        (ofZeroScalar (LinearMap.range K.d₁.hom) x).multiplicity
          (rangeOfZeroScalar_homology_isFiniteLength K.d₁.hom x hMx 0)
          (rangeOfZeroScalar_homology_isFiniteLength K.d₁.hom x hMx 1) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
