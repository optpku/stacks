/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

universe u v w x

namespace associatedPrimesOfModule.Restriction

/-- If an exact associated prime `P` of `M'` lies over `p`, contracts to an exact
associated prime of `M`, and contains the image of no unit `g`, then any bound
controlling exact associated primes that avoid `g` also bounds `p`. -/
@[stacks 0CU7]
theorem le_of_liesOver_of_isUnit
    {A : Type u} {B : Type v} {M : Type w} {M' : Type x}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module B M']
    (g : A) (q p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (hg : IsUnit (algebraMap A B g))
    (h_contract : ∀ Q ∈ associatedPrimesOfModule B M',
      Q.under A ∈ associatedPrimesOfModule A M)
    (h_control : ∀ r ∈ associatedPrimesOfModule A M, g ∉ r → r ≤ q)
    (hP : P ∈ associatedPrimesOfModule B M') :
    p ≤ q := sorry

end associatedPrimesOfModule.Restriction
