/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.UniqueFactorizationDomain.RegularLocal

@[expose] public section

universe u

namespace IsRegularLocalRing

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- In a two-dimensional regular local ring, a proper ideal with reduced quotient is zero,
the maximal ideal, or principal with a nonzero generator in the maximal ideal. -/
theorem ideal_eq_bot_or_maximalIdeal_or_span
    (hdim : ringKrullDim A = 2) (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) [IsReduced (A ⧸ I)] :
    I = ⊥ ∨ I = IsLocalRing.maximalIdeal A ∨
      ∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧ I = Ideal.span {f} := sorry

/-- In a two-dimensional regular local ring, a proper ideal with depth-one quotient is principal
with a nonzero generator in the maximal ideal. -/
theorem ideal_eq_span_of_quotient_depth_eq_one
    (hdim : ringKrullDim A = 2) (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A)
    (hdepth : moduleDepth A (A ⧸ I) = 1) :
    ∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧ I = Ideal.span {f} := sorry

end IsRegularLocalRing
