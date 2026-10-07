module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Module

@[expose] public section

universe u

open IsLocalRing

namespace Ideal.AssociatedGraded

/-- If a filtered element has a nonzerodivisor initial class in the associated
graded ring of a Noetherian local ring, then the filtered element is a
nonzerodivisor in the original ring. -/
theorem mem_nonZeroDivisors_of_stageClass
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {d : ℕ} {x : A} (hx : x ∈ stage (maximalIdeal A) A d)
    (hgr : stageClass (maximalIdeal A) d ⟨x, hx⟩ ∈
      nonZeroDivisors (ring (maximalIdeal A))) :
    x ∈ nonZeroDivisors A := sorry

/-- If a Noetherian local ring contains a nonzerodivisor in its maximal ideal,
eventual injectivity of multiplication by a filtered element's initial class
on the associated graded pieces implies that the filtered element is a
nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_pieceMul_injective_eventually
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {d : ℕ} {x : A} (hx : x ∈ stage (maximalIdeal A) A d)
    (h_nzd : ∃ y ∈ maximalIdeal A, y ∈ nonZeroDivisors A)
    (h_high : ∃ N, ∀ n ≥ N, Function.Injective
      (pieceMul (maximalIdeal A) d n (Submodule.Quotient.mk ⟨x, hx⟩))) :
    x ∈ nonZeroDivisors A := sorry

end Ideal.AssociatedGraded
