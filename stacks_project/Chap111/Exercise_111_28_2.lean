/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Parameters
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open IsLocalRing

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Exercise 111.28.2 (1): if `x` is a nonzerodivisor in the maximal ideal of a Noetherian
local ring `R` of Krull dimension 1, then `ringKrullDim (R ⧸ Ideal.span {x}) = 0`. -/
@[stacks 02EG]
theorem ringKrullDim_quotient_span_singleton_eq_zero_of_mem_nonZeroDivisors
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {x}) = 0 := sorry

/-- If `x` is a nonzerodivisor in the maximal ideal of a Noetherian local ring of Krull
dimension 1, then the quotient `R ⧸ Ideal.span {x}` is an Artinian ring. -/
theorem isArtinianRing_quotient_span_singleton_of_mem_nonZeroDivisors
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R) :
    IsArtinianRing (R ⧸ Ideal.span {x}) := sorry

/-- If `x` is a nonzerodivisor in the maximal ideal of a Noetherian local ring of Krull
dimension 1, then the singleton family `fun _ : Fin 1 ↦ ⟨x, hxm⟩` is a system of parameters. -/
theorem isSystemOfParameters_singleton_of_mem_nonZeroDivisors
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R) :
    IsSystemOfParameters (fun _ : Fin 1 ↦ ⟨x, hxm⟩) := sorry

/-- Given a Noetherian local ring of Krull dimension 1, a singleton family in the maximal
ideal is a system of parameters if and only if the corresponding principal quotient has
Krull dimension 0. -/
theorem isSystemOfParameters_singleton_iff_ringKrullDim_quotient_eq_zero
    (hdim : ringKrullDim R = 1) {x : R} (hxm : x ∈ maximalIdeal R) :
    IsSystemOfParameters (fun _ : Fin 1 ↦ ⟨x, hxm⟩) ↔
      ringKrullDim (R ⧸ Ideal.span {x}) = 0 := sorry

/-- Exercise 111.28.2 (2): if a Noetherian local ring of Krull dimension 1 has a
nonzerodivisor in its maximal ideal, then it has no embedded prime. -/
@[stacks 02EG]
theorem embeddedPrimes_eq_empty_of_mem_nonZeroDivisors
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R) :
    embeddedPrimes R = ∅ := sorry

/-- Exercise 111.28.2 (3): a Noetherian local ring of Krull dimension 1 with no embedded
prime has a nonzerodivisor in its maximal ideal. -/
@[stacks 02EG]
theorem exists_mem_maximalIdeal_mem_nonZeroDivisors_of_embeddedPrimes_eq_empty
    (hdim : ringKrullDim R = 1) (hembedded : embeddedPrimes R = ∅) :
    ∃ x ∈ maximalIdeal R, x ∈ nonZeroDivisors R := sorry

/-- For a Noetherian local ring of Krull dimension 1, existence of a nonzerodivisor in the
maximal ideal is equivalent to having no embedded prime. -/
theorem exists_mem_maximalIdeal_mem_nonZeroDivisors_iff_embeddedPrimes_eq_empty
    (hdim : ringKrullDim R = 1) :
    (∃ x ∈ maximalIdeal R, x ∈ nonZeroDivisors R) ↔ embeddedPrimes R = ∅ := sorry

end IsLocalRing
