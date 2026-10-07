module

public import Mathlib.RingTheory.Smooth.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Polynomial conormal criteria for formal smoothness

@stack 031I

This source-facing bridge keeps the conormal presentation visible and delegates the core
split-injection criterion to `Algebra.FormallySmooth.iff_split_injection`.
-/

open scoped TensorProduct

universe u v w

section

variable (R : Type u) (ι : Type v) (S : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

/- Lemma 10.138.7: for a surjective polynomial presentation `MvPolynomial ι R → S`, formal
smoothness of `S` over `R` is equivalent to split exactness of the conormal sequence. The
canonical theorem expresses the same condition as a retraction of
`KaehlerDifferential.kerCotangentToTensor`. -/
@[stacks 031I]
#check Algebra.FormallySmooth.iff_split_injection
  (R := R) (P := MvPolynomial ι R) (A := S)

end
