/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Localized determinants of two-periodic complexes

This file records the determinant of a two-periodic endomorphism complex at a minimal point of
its support and its order over the corresponding prime quotient.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The periodic determinant of a two-periodic complex after localization at a minimal point of
its one-dimensional support. -/
noncomputable def localizedDeterminantAt
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R K.X) q) : q.asIdeal.ResidueFieldˣ :=
  (localizedAtPrime K q).determinant
    (localizedAtPrime_isFiniteLength K q hq)
    (localizedAtPrime_acyclic K h₀ h₁ hdim q hq)

/-- The localized determinant is the periodic determinant of the explicitly localized complex. -/
theorem localizedDeterminantAt_def
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R K.X) q) :
    localizedDeterminantAt K h₀ h₁ hdim q hq =
      (localizedAtPrime K q).determinant
        (localizedAtPrime_isFiniteLength K q hq)
        (localizedAtPrime_acyclic K h₀ h₁ hdim q hq) := sorry

/-- The integer order of the localized periodic determinant at a minimal point of the support. -/
noncomputable def determinantOrderAt
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R K.X) q) : ℤ :=
  -- Local instance justification (proof-local temporary data): support dimension and minimality give the pointwise quotient dimension required by `Ring.ordFrac`.
  letI : Ring.KrullDimLE 1 (R ⧸ q.asIdeal) :=
    (Ring.krullDimLE_iff).2
      (((Module.supportDim_quotient_eq_ringKrullDim q.asIdeal).symm.trans
        (Module.supportDim_quotient_eq_one_of_minimalSupport K.X hdim q hq)).le.trans_eq rfl)
  WithZero.log (Ring.ordFrac (R ⧸ q.asIdeal)
    (localizedDeterminantAt K h₀ h₁ hdim q hq : q.asIdeal.ResidueField))

/-- The localized determinant order is computed by the order of vanishing over the corresponding
prime quotient. -/
theorem determinantOrderAt_def
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R K.X) q) :
    determinantOrderAt K h₀ h₁ hdim q hq =
      -- Local instance justification (proof-local temporary data): support dimension and minimality give the pointwise quotient dimension required by `Ring.ordFrac`.
      letI : Ring.KrullDimLE 1 (R ⧸ q.asIdeal) :=
        (Ring.krullDimLE_iff).2
          (((Module.supportDim_quotient_eq_ringKrullDim q.asIdeal).symm.trans
            (Module.supportDim_quotient_eq_one_of_minimalSupport K.X hdim q hq)).le.trans_eq rfl)
      WithZero.log (Ring.ordFrac (R ⧸ q.asIdeal)
        (localizedDeterminantAt K h₀ h₁ hdim q hq : q.asIdeal.ResidueField)) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
