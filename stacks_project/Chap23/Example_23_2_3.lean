/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Padic
import StacksCheckRecall

@[expose] public section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] [Algebra ℤ_[p] A]

/- Example 23.2.3 (07GN): a `ℤ_[p]`-algebra has unique divided powers on `(p)`, with the
coefficient `p ^ n / n !` represented canonically inside `ℤ_[p]` by
`(PadicInt.dividedPowers p).dpow n p`. -/
@[stacks 07GN]
#check (PadicInt.existsUnique_dividedPowers_span_prime (p := p) (A := A) :
  ∃! gamma : DividedPowers (Ideal.span ({(p : A)} : Set A)),
    ∀ (n : ℕ) (a : A),
      gamma.dpow n ((p : A) * a) =
        algebraMap ℤ_[p] A ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) * a ^ n)

#check @PadicInt.coe_dpow_eq_of_mem
#check @PadicInt.dividedPowers_extends_algebraMap
#check @PadicInt.isDPMorphism_iff_dpow_mul
#check @PadicInt.dividedPowers_eq_of_isDPMorphism
