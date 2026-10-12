/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
# Divided-power polynomial algebras

The reusable indexed construction and its finite-variable specialization are owned by
`DPPolynomial`.  This file records the two clauses of Lemma 23.5.1 directly against that
canonical API.
-/

open DividedPowers

noncomputable section

universe uA uW

section Source

variable (A : Type uA) [CommRing A] (I : Ideal A) (γ : DividedPowers I) (t : ℕ)

/- Lemma 23.5.1 (1) (07H5): the ideal obtained by extending the base divided-power ideal and
adjoining all positive formal divided powers has a unique compatible divided-power structure. -/
@[stacks 07H5 "(1)"] #check
  (DPPolynomial.Finite.existsUnique_dividedPowers (n := t) γ :
    ∃! delta : DividedPowers (DPPolynomial.Finite.ideal A t I),
      DPPolynomial.Finite.IsCanonical γ delta)

variable {C : Type uW} [CommRing C] (K : Ideal C) (ε : DividedPowers K)
variable (f : DPMorphism γ ε) (x : Fin t → K)

/- Lemma 23.5.1 (2) (07H5): a divided-power morphism out of the finite divided-power polynomial
algebra is uniquely determined by its base map and the images of its variables. -/
@[stacks 07H5 "(2)"] #check
  (DPPolynomial.Finite.existsUnique_lift f x :
    ∃! phi : DPPolynomial.Finite.Ring A t →+* C,
      DPPolynomial.Finite.IsLift
        (DPPolynomial.Finite.dividedPowers (n := t) γ) f x phi)

end Source

#check @DPPolynomial.Finite.existsUnique_dividedPowers
#check @DPPolynomial.Finite.existsUnique_lift
#check @DPPolynomial.Finite.Ring
#check @DPPolynomial.Finite.X
#check @DPPolynomial.Finite.dp
#check @DPPolynomial.Finite.positiveIdeal
#check @DPPolynomial.Finite.ideal
#check @DPPolynomial.Finite.IsCanonical
#check @DPPolynomial.Finite.dividedPowers
#check @DPPolynomial.Finite.dividedPowers_isCanonical
#check @DPPolynomial.Finite.isCanonical_iff_eq_dividedPowers
#check @DPPolynomial.IsCanonical.dpow_X
#check @DPPolynomial.IsCanonical.algebraMap_isDPMorphism
#check @DPPolynomial.dividedPowers
#check @DPPolynomial.dividedPowers_isCanonical
#check @DPPolynomial.dividedPowers_dpow_X
#check @DPPolynomial.dividedPowers_dpow_algebraMap
#check @DPPolynomial.dividedPowers_dpow_dp
#check @DPPolynomial.isCanonical_iff_eq_dividedPowers
#check @DPPolynomial.exists_isCanonical
#check @DPPolynomial.IsCanonical.eq
#check @DPPolynomial.Finite.lift
#check @DPPolynomial.Finite.dpLift
#check @DPPolynomial.Finite.IsLift
#check @DPPolynomial.dpLift
#check @DPPolynomial.dpLift_X
#check @DPPolynomial.dpLift_apply_dp
#check @DPPolynomial.dpLift_unique
