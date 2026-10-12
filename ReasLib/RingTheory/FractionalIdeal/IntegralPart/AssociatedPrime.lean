/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FractionalIdeal.IntegralPart
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded
public import ReasLib.RingTheory.Normal.Serre
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated primes of integral parts of fractional ideals

These statements are owned by the contracted fractional ideal, not by a chosen presentation
`R ∩ xR`.  They apply to any principal fractional ideal in any chosen fraction-field model.

@stack 031T
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

universe u v

namespace FractionalIdeal.IntegralPart.Quotient

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsNormalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- The quotient by the integral part of a principal fractional ideal in a Noetherian normal
domain has no embedded associated primes. -/
@[stacks 031T "principal fractional ideals have no embedded primes"]
theorem noEmbedded_of_isPrincipal
    (I : FractionalIdeal R⁰ K) [Submodule.IsPrincipal (I : Submodule R K)] :
    embeddedAssociatedPrimes R (R ⧸ I.integralPart) = ∅ := sorry

/-- Associated primes of the quotient by the integral part of a nonzero principal fractional
ideal have height one. -/
@[stacks 031T "height for a principal fractional ideal"]
theorem associatedPrime_height_of_isPrincipal
    (I : FractionalIdeal R⁰ K) [Submodule.IsPrincipal (I : Submodule R K)]
    (hI : I ≠ 0) {p : Ideal R}
    (hp : p ∈ associatedPrimes R (R ⧸ I.integralPart)) :
    p.height = 1 := sorry

/-- The no-embedded-primes statement for a fractional ideal given by an explicit generator. -/
@[stacks 031T "integral part of a generated fractional ideal"]
theorem spanSingleton_noEmbedded (x : K) :
    embeddedAssociatedPrimes R
      (R ⧸ (FractionalIdeal.spanSingleton R⁰ x).integralPart) = ∅ := by
  -- The generic theorem follows Mathlib's typeclass API for principal submodules; this witness is
  -- determined by the displayed generator and is used only for the specialization
  -- (proof-local temporary data).
  letI : Submodule.IsPrincipal
      ((FractionalIdeal.spanSingleton R⁰ x : FractionalIdeal R⁰ K) : Submodule R K) :=
    (FractionalIdeal.isPrincipal_iff _).mpr ⟨x, rfl⟩
  exact noEmbedded_of_isPrincipal (FractionalIdeal.spanSingleton R⁰ x)

/-- The height statement for a nonzero explicit generator. -/
@[stacks 031T "height for a generated fractional ideal"]
theorem spanSingleton_associatedPrime_height
    {x : K} (hx : x ≠ 0) {p : Ideal R}
    (hp : p ∈ associatedPrimes R
      (R ⧸ (FractionalIdeal.spanSingleton R⁰ x).integralPart)) :
    p.height = 1 := by
  -- The generic theorem follows Mathlib's typeclass API for principal submodules; this witness is
  -- determined by the displayed generator and is used only for the specialization
  -- (proof-local temporary data).
  letI : Submodule.IsPrincipal
      ((FractionalIdeal.spanSingleton R⁰ x : FractionalIdeal R⁰ K) : Submodule R K) :=
    (FractionalIdeal.isPrincipal_iff _).mpr ⟨x, rfl⟩
  exact associatedPrime_height_of_isPrincipal
    (FractionalIdeal.spanSingleton R⁰ x)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hp

end FractionalIdeal.IntegralPart.Quotient
