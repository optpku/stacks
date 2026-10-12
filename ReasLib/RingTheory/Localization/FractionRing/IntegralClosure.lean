/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Relative.Noetherian
public import ReasLib.RingTheory.LocalRing.ResidueField.FractionRing
public import ReasLib.RingTheory.LocalRing.ResidueField.LiesOver

/-!
# Integral closures in finite fraction-field extensions

The integral closure of a one-dimensional Noetherian domain in a finite
extension of its fraction field is Dedekind, with finite prime fibers and
finite residue-field extensions.  For a semilocal domain, these results
specialize to `integralClosure B (FractionRing B)`.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u v

namespace FractionRing.IntegralClosure

variable {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
variable [Finite (MaximalSpectrum B)]

/-- The integral closure of a one-dimensional Noetherian domain in a finite
fraction-field extension is a Dedekind domain. -/
@[stacks 09IG "Dedekind integral closure in a finite fraction-field extension"]
theorem isDedekind_of_finite_extension
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Ring.DimensionLEOne A] :
    IsDedekindDomain (integralClosure A L) := sorry

/-- The map on prime spectra from an
integral closure in a common fraction-field extension is surjective. This
only uses integrality and injectivity of the normalization map. -/
@[stacks 09IG "integral-closure spectrum surjectivity"]
theorem spectrum_comap_surjective
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (integralClosure A L))) := by
  apply RingHom.IsIntegral.comap_surjective
  · exact algebraMap_isIntegral_iff.mpr inferInstance
  · exact algebraMap_injective_of_field_isFractionRing
      A (integralClosure A L) (FractionRing A) L

/-- The primes of an integral closure lying over any prime of a
one-dimensional Noetherian domain form a finite set. -/
@[stacks 09IG "finite prime fibers of a finite integral closure"]
theorem primesOver_finite_of_dim_one
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Ring.DimensionLEOne A]
    (p : Ideal A) [p.IsPrime] :
    (p.primesOver (integralClosure A L)).Finite := sorry

/-- For every prime of the integral closure in a finite extension
of the fraction field of a one-dimensional Noetherian domain, the induced
residue-field extension over its contraction is finite. -/
@[stacks 09IG "residue-field finiteness of a finite integral closure"]
theorem residueField_finite_of_dim_one
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Ring.DimensionLEOne A]
    (q : PrimeSpectrum (integralClosure A L)) :
    -- Local instance justification (instance diamond): the residue algebra depends on the
    -- selected lying-over prime and is therefore kept scoped to this finiteness statement.
    letI : Algebra
        (PrimeSpectrum.comap (algebraMap A (integralClosure A L)) q).asIdeal.ResidueField
        q.asIdeal.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver
        (PrimeSpectrum.comap (algebraMap A (integralClosure A L)) q).asIdeal q.asIdeal
    Module.Finite
      (PrimeSpectrum.comap (algebraMap A (integralClosure A L)) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := sorry

/-- The integral closure of a semilocal Noetherian
one-dimensional domain in its fraction field is a Dedekind domain. -/
@[stacks 09N2]
theorem isDedekind_of_dim_one (hdim : ringKrullDim B = 1) :
    IsDedekindDomain (integralClosure B (FractionRing B)) := sorry

/-- The integral closure of a semilocal Noetherian
one-dimensional domain in its fraction field is semilocal. -/
@[stacks 09N2]
theorem finiteMaximalSpectrum_of_dim_one (hdim : ringKrullDim B = 1) :
    Finite (MaximalSpectrum (integralClosure B (FractionRing B))) := sorry

/-- A nonzero Jacobson-radical element of the integral
closure of a semilocal Noetherian one-dimensional domain clears every element
back into the base ring after a power. -/
@[stacks 09N2]
theorem exists_pow_mul_mem_base_of_mem_jacobson
    (hdim : ringKrullDim B = 1) (x y : integralClosure B (FractionRing B))
    (hx : x ∈ Ring.jacobson (integralClosure B (FractionRing B))) (hx0 : x ≠ 0) :
    ∃ n : ℕ, ∃ b : B, algebraMap B (integralClosure B (FractionRing B)) b = x ^ n * y := sorry

end FractionRing.IntegralClosure
