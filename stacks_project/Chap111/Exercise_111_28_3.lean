/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.DoubleLine
public import ReasLib.RingTheory.MvPolynomial.LineWithEmbeddedPoint
import StacksCheckRecall

/-!
# Exercise 111.28.3

Cohen-Macaulay rings of dimension 1, Part II: two local examples in the
affine plane, localized at the origin `(x, y)`.
-/

@[expose] public section

noncomputable section

universe u

open IsLocalRing

/- Exercise 111.28.3 (1): the local ring `A` at `(x, y)` of `k[x, y] ⧸ (x ^ 2, x * y)` has Krull dimension `1`. -/
@[stacks 02EH]
#check (MvPolynomial.LineWithEmbeddedPoint.ringKrullDim_localRing :
  ∀ (k : Type u) [Field k],
    ringKrullDim (MvPolynomial.LineWithEmbeddedPoint.LocalRing k) = 1)

/- Exercise 111.28.3 (2): every element of the maximal ideal `m ⊂ A` of the local ring is a zerodivisor. -/
@[stacks 02EH]
#check (MvPolynomial.LineWithEmbeddedPoint.notMem_nonZeroDivisors_of_mem_maximalIdeal :
  ∀ (k : Type u) [Field k] {a : MvPolynomial.LineWithEmbeddedPoint.LocalRing k},
    a ∈ IsLocalRing.maximalIdeal (MvPolynomial.LineWithEmbeddedPoint.LocalRing k) →
      a ∉ nonZeroDivisors (MvPolynomial.LineWithEmbeddedPoint.LocalRing k))

/- Exercise 111.28.3 (3): the image `yParam` of `y` lies in the maximal ideal of the local ring, and the quotient by `yParam` has Krull dimension `0`. -/
@[stacks 02EH]
#check (MvPolynomial.LineWithEmbeddedPoint.yParam_spec :
  ∀ (k : Type u) [Field k],
    MvPolynomial.LineWithEmbeddedPoint.yParam k ∈
        IsLocalRing.maximalIdeal (MvPolynomial.LineWithEmbeddedPoint.LocalRing k) ∧
      ringKrullDim
          (MvPolynomial.LineWithEmbeddedPoint.LocalRing k ⧸
            Ideal.span {MvPolynomial.LineWithEmbeddedPoint.yParam k}) = 0)

/- Exercise 111.28.3 (4): the image `yParam` of `y` in the local ring at `(x, y)` of `k[x, y] ⧸ (x ^ 2)` is a nonzerodivisor in the maximal ideal. -/
@[stacks 02EH]
#check (MvPolynomial.DoubleLine.yParam_spec :
  ∀ (k : Type u) [Field k],
    MvPolynomial.DoubleLine.yParam k ∈
        IsLocalRing.maximalIdeal (MvPolynomial.DoubleLine.LocalRing k) ∧
      MvPolynomial.DoubleLine.yParam k ∈
        nonZeroDivisors (MvPolynomial.DoubleLine.LocalRing k))
