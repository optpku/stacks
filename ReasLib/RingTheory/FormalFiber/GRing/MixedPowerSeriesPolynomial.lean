module

public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.FieldTheory.PBasis.MixedPowerSeries.Properties
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal fibers of mixed power-series/polynomial rings

@stack 07PR

The generic formal fiber of a completed localization of a mixed power-series/polynomial ring is
geometrically regular over the fraction field.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace FieldExtension.PBasis.mixedPowerSeriesPolynomialRing

/-- Lemma 15.50.5 (Stacks `07PR`): for
`A = k[[x₁, …, xₙ]][y₁, …, yₘ]`, every generic formal fiber
`R̂[𝔭] ⊗[A] K` is geometrically regular over a fraction field `K` of `A`. -/
@[stacks 07PR]
theorem formalFiber_fractionRing_isGeometricallyRegular
    {p : ℕ} [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (n m : ℕ)
    (𝔭 : PrimeSpectrum (mixedPowerSeriesPolynomialRing (Fin n) (Fin m) k))
    {K : Type u} [Field K]
    [Algebra (mixedPowerSeriesPolynomialRing (Fin n) (Fin m) k) K]
    [IsFractionRing (mixedPowerSeriesPolynomialRing (Fin n) (Fin m) k) K] :
    -- Local instance justification (search instability): pin the canonical completion algebra
    -- before the tensor-product ring structure is inferred.
    letI : Algebra (mixedPowerSeriesPolynomialRing (Fin n) (Fin m) k) R̂[𝔭] :=
      inferInstance
    -- Local instance justification (instance diamond): geometric regularity uses the action of
    -- the right-hand fraction-field factor.
    letI : Algebra K
        (R̂[𝔭] ⊗[mixedPowerSeriesPolynomialRing (Fin n) (Fin m) k] K) :=
      Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular K
      (R̂[𝔭] ⊗[mixedPowerSeriesPolynomialRing (Fin n) (Fin m) k] K) := sorry

end FieldExtension.PBasis.mixedPowerSeriesPolynomialRing
