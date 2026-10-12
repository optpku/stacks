/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Localization.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Multiplicity
public import ReasLib.RingTheory.Module.Support.LocalDimensionOne

/-!
# Localized determinants of zero-first-differential two-periodic complexes

This file specializes localized determinant units and their orders to the two-periodic complex
associated to a module endomorphism whose first differential is zero.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The determinant unit of an endomorphism localized at a nonclosed point of its
one-dimensional support. -/
noncomputable def ofZeroDeterminantAt (M : ModuleCat.{v} R) [Module.Finite R M] (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R))
    (hdim : Module.supportDim R M ≤ 1) (q : PrimeSpectrum R)
    (hq_mem : q ∈ Module.support R M)
    (hq_ne_closedPoint : q ≠ IsLocalRing.closedPoint R) : q.asIdeal.ResidueFieldˣ :=
  -- Local instance justification (defeq pin): `ofZero ψ` has carrier `M`, whose finiteness instance is already available.
  letI : Module.Finite R (ofZero ψ).X := inferInstanceAs (Module.Finite R M)
  (localizedDeterminantAt (ofZero ψ) (ofZero_homology_zero_isFiniteLength ψ hCoker)
    (ofZero_homology_one_isFiniteLength ψ hKer)
    (Module.supportDim_eq_one_of_mem_ne_closedPoint hdim q hq_mem hq_ne_closedPoint) q
    (Module.minimal_of_mem_support_of_ne_closedPoint_of_supportDim_le_one
      hdim q hq_mem hq_ne_closedPoint))⁻¹

/-- The determinant unit of `ofZero ψ` is the inverse of its localized periodic determinant. -/
theorem ofZeroDeterminantAt_def (M : ModuleCat.{v} R) [Module.Finite R M] (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R))
    (hdim : Module.supportDim R M ≤ 1) (q : PrimeSpectrum R)
    (hq_mem : q ∈ Module.support R M)
    (hq_ne_closedPoint : q ≠ IsLocalRing.closedPoint R) :
    ofZeroDeterminantAt M ψ hCoker hKer hdim q hq_mem hq_ne_closedPoint =
      -- Local instance justification (defeq pin): `ofZero ψ` has carrier `M`, whose finiteness instance is already available.
      letI : Module.Finite R (ofZero ψ).X := inferInstanceAs (Module.Finite R M)
      (localizedDeterminantAt (ofZero ψ)
        (ofZero_homology_zero_isFiniteLength ψ hCoker)
        (ofZero_homology_one_isFiniteLength ψ hKer)
        (Module.supportDim_eq_one_of_mem_ne_closedPoint hdim q hq_mem hq_ne_closedPoint) q
        (Module.minimal_of_mem_support_of_ne_closedPoint_of_supportDim_le_one
          hdim q hq_mem hq_ne_closedPoint))⁻¹ := sorry

/-- After coercion to the residue field, `ofZeroDeterminantAt` is the finite-length determinant
of the localized endomorphism. -/
theorem ofZeroDeterminantAt_coe (M : ModuleCat.{v} R) [Module.Finite R M] (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R))
    (hdim : Module.supportDim R M ≤ 1) (q : PrimeSpectrum R)
    (hq_mem : q ∈ Module.support R M)
    (hq_ne_closedPoint : q ≠ IsLocalRing.closedPoint R) :
    (ofZeroDeterminantAt M ψ hCoker hKer hdim q hq_mem hq_ne_closedPoint :
        q.asIdeal.ResidueField) =
      -- Local instance justification (defeq pin): `ofZero ψ` has carrier `M`, whose finiteness instance is already available.
      letI : Module.Finite R (ofZero ψ).X := inferInstanceAs (Module.Finite R M)
      Module.End.finiteLengthDeterminant (LocalizedModule.map q.asIdeal.primeCompl ψ.hom)
        (localizedAtPrime_isFiniteLength (ofZero ψ) q
          (Module.minimal_of_mem_support_of_ne_closedPoint_of_supportDim_le_one
            hdim q hq_mem hq_ne_closedPoint)) := sorry

/-- The order of vanishing of the localized determinant unit attached to `ofZero ψ`. -/
noncomputable def ofZeroDeterminantOrderAt
    (M : ModuleCat.{v} R) [Module.Finite R M] (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R))
    (hdim : Module.supportDim R M ≤ 1) (q : PrimeSpectrum R)
    (hq_mem : q ∈ Module.support R M)
    (hq_ne_closedPoint : q ≠ IsLocalRing.closedPoint R) : ℤ :=
  -- Local instance justification (proof-local temporary data): the support bound at `q` gives the quotient-dimension instance required by `Ring.ordFrac`.
  letI : Ring.KrullDimLE 1 (R ⧸ q.asIdeal) :=
    (Ring.krullDimLE_iff).2
      ((Module.quotientDim_le_supportDim_of_mem q hq_mem).trans hdim)
  WithZero.log (Ring.ordFrac (R ⧸ q.asIdeal)
    (ofZeroDeterminantAt M ψ hCoker hKer hdim q hq_mem hq_ne_closedPoint :
      q.asIdeal.ResidueField))

/-- The localized determinant order is computed by `Ring.ordFrac` over the corresponding prime
quotient. -/
theorem ofZeroDeterminantOrderAt_def
    (M : ModuleCat.{v} R) [Module.Finite R M] (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R))
    (hdim : Module.supportDim R M ≤ 1) (q : PrimeSpectrum R)
    (hq_mem : q ∈ Module.support R M)
    (hq_ne_closedPoint : q ≠ IsLocalRing.closedPoint R) :
    ofZeroDeterminantOrderAt M ψ hCoker hKer hdim q hq_mem hq_ne_closedPoint =
      -- Local instance justification (proof-local temporary data): the support bound at `q` gives the quotient-dimension instance required by `Ring.ordFrac`.
      letI : Ring.KrullDimLE 1 (R ⧸ q.asIdeal) :=
        (Ring.krullDimLE_iff).2
          ((Module.quotientDim_le_supportDim_of_mem q hq_mem).trans hdim)
      WithZero.log (Ring.ordFrac (R ⧸ q.asIdeal)
        (ofZeroDeterminantAt M ψ hCoker hKer hdim q hq_mem hq_ne_closedPoint :
          q.asIdeal.ResidueField)) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
