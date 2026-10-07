module

public import ReasLib.RingTheory.DividedPowers.Tate
import StacksCheckRecall

@[expose] public section

universe u v w

section Existence

variable {R : Type u} {S : Type w} {J : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (pi0 : MvPolynomial J R →ₐ[R] S) (hpi0 : Function.Surjective pi0)

/- Lemma 23.6.9 (Tag 09PN) (1): a chosen surjection `R[x_j] → S` extends to a Tate resolution.
The reusable owner uses a strictly commutative chain DGA, genuine divided powers on its positive
even part, a free graded divided-power presentation, and a quasi-isomorphic augmentation to `S`.
-/
@[stacks 09PN "(1)"]
#check (TateResolution.nonempty pi0 hpi0 :
  Nonempty (TateResolution.{u, v, w} pi0))

end Existence

section Finite

variable {R : Type u} {S : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]

/- Lemma 23.6.9 (Tag 09PN) (2): under the Noetherian finite-type hypotheses, a polynomial
presentation and its Tate resolution can be chosen with finitely many generators in every degree.
-/
@[stacks 09PN "(2)"]
#check (TateResolution.exists_finitePresentation (R := R) (S := S) :
  ∃ (n : ℕ) (pi0 : MvPolynomial (Fin n) R →ₐ[R] S),
    Function.Surjective pi0 ∧
      ∃ A : TateResolution.{u, 0, w} pi0, A.HasFinitePositiveGenerators)

end Finite

#check @TateResolution.exists_finite

#check @DividedPowerChainAlgebra
#check @DividedPowerGradedAlgebra.FreePresentation
#check @DividedPowerGradedAlgebra.FreePresentation.comparison
#check @DividedPowerGradedAlgebra.FreePresentation.comparisonIso
#check @TateResolution
#check @TateResolution.Positive
