/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant of an exact two-periodic complex

The two canonical range--term--range short exact rows give determinant-line equivalences in
opposite tensor orders. Commuting the tensor factors between them produces the determinant-line
automorphism whose signed determinant is the invariant.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The inclusion of `range d₁` followed by `d₀` restricted to its range is zero. -/
theorem range_d₁_comp_rangeRestrict_d₀
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) :
    ModuleCat.ofHom (LinearMap.range K.d₁.hom).subtype ≫
      ModuleCat.ofHom K.d₀.hom.rangeRestrict = 0 := sorry

/-- The canonical range--term--range row associated to the differential `d₀`. -/
def d₀RangeSequence (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.range K.d₁.hom).subtype)
    (ModuleCat.ofHom K.d₀.hom.rangeRestrict)
    (range_d₁_comp_rangeRestrict_d₀ K)

/-- The inclusion of `range d₀` followed by `d₁` restricted to its range is zero. -/
theorem range_d₀_comp_rangeRestrict_d₁
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) :
    ModuleCat.ofHom (LinearMap.range K.d₀.hom).subtype ≫
      ModuleCat.ofHom K.d₁.hom.rangeRestrict = 0 := sorry

/-- The canonical range--term--range row associated to the differential `d₁`. -/
def d₁RangeSequence (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.range K.d₀.hom).subtype)
    (ModuleCat.ofHom K.d₁.hom.rangeRestrict)
    (range_d₀_comp_rangeRestrict_d₁ K)

/-- Exactness of a two-periodic complex makes its `d₀` range row short exact. -/
theorem d₀RangeSequence_shortExact
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hK : K.toCochainComplex.Acyclic) : (d₀RangeSequence K).ShortExact := sorry

/-- Exactness of a two-periodic complex makes its `d₁` range row short exact. -/
theorem d₁RangeSequence_shortExact
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hK : K.toCochainComplex.Acyclic) : (d₁RangeSequence K).ShortExact := sorry

/-- The range of `d₀` has finite length when the underlying module does. -/
theorem range_d₀_isFiniteLength
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) : IsFiniteLength R (LinearMap.range K.d₀.hom) := sorry

/-- The range of `d₁` has finite length when the underlying module does. -/
theorem range_d₁_isFiniteLength
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) : IsFiniteLength R (LinearMap.range K.d₁.hom) := sorry

/-- The determinant-line automorphism `γψ ∘ σ ∘ γφ⁻¹` of an exact finite-length
two-periodic endomorphism complex. -/
def determinantComparison
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic) :
    Module.FiniteLengthDeterminant R K.X hM ≃ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R K.X hM :=
  let hI₀ := range_d₀_isFiniteLength K hM
  let hI₁ := range_d₁_isFiniteLength K hM
  let γφ := Module.FiniteLengthDeterminant.exactEquiv
    (d₀RangeSequence K) hI₁ hM hI₀ (d₀RangeSequence_shortExact K hK)
  let γψ := Module.FiniteLengthDeterminant.exactEquiv
    (d₁RangeSequence K) hI₀ hM hI₁ (d₁RangeSequence_shortExact K hK)
  γφ.symm |>.trans (TensorProduct.comm (IsLocalRing.ResidueField R) _ _) |>.trans γψ

/-- The defining `γψ ∘ σ ∘ γφ⁻¹` formula for `determinantComparison`. -/
theorem determinantComparison_def
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic) :
    determinantComparison K hM hK =
      let hI₀ := range_d₀_isFiniteLength K hM
      let hI₁ := range_d₁_isFiniteLength K hM
      let γφ := Module.FiniteLengthDeterminant.exactEquiv
        (d₀RangeSequence K) hI₁ hM hI₀ (d₀RangeSequence_shortExact K hK)
      let γψ := Module.FiniteLengthDeterminant.exactEquiv
        (d₁RangeSequence K) hI₀ hM hI₁ (d₁RangeSequence_shortExact K hK)
      γφ.symm |>.trans (TensorProduct.comm (IsLocalRing.ResidueField R) _ _) |>.trans γψ := sorry

/-- The determinant of an exact finite-length two-periodic endomorphism complex. -/
noncomputable def determinant
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic) :
    (IsLocalRing.ResidueField R)ˣ :=
  (-1) ^ ((Module.length R (LinearMap.range K.d₀.hom)).toNat *
      (Module.length R (LinearMap.range K.d₁.hom)).toNat) *
    LinearEquiv.det (determinantComparison K hM hK)

/-- The signed linear-equivalence determinant formula defining `determinant`. -/
theorem determinant_def
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic) :
    determinant K hM hK =
      (-1) ^ ((Module.length R (LinearMap.range K.d₀.hom)).toNat *
          (Module.length R (LinearMap.range K.d₁.hom)).toNat) *
        LinearEquiv.det (determinantComparison K hM hK) := sorry

/-- The canonical determinant-line comparison is multiplication by the parity sign of the two
differential-image lengths times `determinant K hM hK`. -/
theorem determinant_spec
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
    (x : Module.FiniteLengthDeterminant R K.X hM) :
    determinantComparison K hM hK x =
      (((-1) ^ ((Module.length R (LinearMap.range K.d₀.hom)).toNat *
          (Module.length R (LinearMap.range K.d₁.hom)).toNat) *
        determinant K hM hK : (IsLocalRing.ResidueField R)ˣ) :
          IsLocalRing.ResidueField R) • x := sorry

/-- For nonzero determinant symbols of the two differential ranges, the two short-exact
concatenations differ by the signed determinant of the exact finite-length two-periodic complex. -/
theorem determinant_symbol
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
    (x : Module.FiniteLengthDeterminant.Symbol R (LinearMap.range K.d₀.hom)
      (range_d₀_isFiniteLength K hM))
    (hx : Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₀.hom)
      (range_d₀_isFiniteLength K hM) x ≠ 0)
    (y : Module.FiniteLengthDeterminant.Symbol R (LinearMap.range K.d₁.hom)
      (range_d₁_isFiniteLength K hM))
    (hy : Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₁.hom)
      (range_d₁_isFiniteLength K hM) y ≠ 0) :
    Module.FiniteLengthDeterminant.exactEquiv (d₁RangeSequence K)
        (range_d₀_isFiniteLength K hM) hM (range_d₁_isFiniteLength K hM)
        (d₁RangeSequence_shortExact K hK)
        (Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₀.hom)
            (range_d₀_isFiniteLength K hM) x ⊗ₜ[IsLocalRing.ResidueField R]
          Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₁.hom)
            (range_d₁_isFiniteLength K hM) y) =
      (((-1) ^ ((Module.length R (LinearMap.range K.d₀.hom)).toNat *
            (Module.length R (LinearMap.range K.d₁.hom)).toNat) *
          determinant K hM hK : (IsLocalRing.ResidueField R)ˣ) :
        IsLocalRing.ResidueField R) •
        Module.FiniteLengthDeterminant.exactEquiv (d₀RangeSequence K)
          (range_d₁_isFiniteLength K hM) hM (range_d₀_isFiniteLength K hM)
          (d₀RangeSequence_shortExact K hK)
          (Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₁.hom)
              (range_d₁_isFiniteLength K hM) y ⊗ₜ[IsLocalRing.ResidueField R]
            Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₀.hom)
              (range_d₀_isFiniteLength K hM) x) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
