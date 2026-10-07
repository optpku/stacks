module

public import ReasLib.RingTheory.Catenary.PrimeSpectrum
public import ReasLib.RingTheory.Ideal.Localization
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 111.18.1 (1): a Noetherian ring `A` is catenary if and only if nested primes
`p₁ ≤ p₂ ≤ p₃` have additive heights of successive images in the quotients `A ⧸ pᵢ`,
measured by `(pⱼ.asIdeal.map (Ideal.Quotient.mk pᵢ.asIdeal)).height`. -/
@[stacks 027O]
#check (isCatenaryRing_iff_height_additive :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A],
    IsCatenaryRing A ↔
      ∀ ⦃p₁ p₂ p₃ : PrimeSpectrum A⦄, p₁ ≤ p₂ → p₂ ≤ p₃ →
        (p₃.asIdeal.map (Ideal.Quotient.mk p₁.asIdeal)).height =
          (p₃.asIdeal.map (Ideal.Quotient.mk p₂.asIdeal)).height +
            (p₂.asIdeal.map (Ideal.Quotient.mk p₁.asIdeal)).height)

/- The Krull dimension of `q.asIdeal.quotientAtPrime p` equals the height of
`p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)`. -/
#check (ringKrullDim_quotientAtPrime_eq_height_map_quotient :
  ∀ {A : Type u} [CommRing A] {p q : PrimeSpectrum A}, q ≤ p →
    ringKrullDim (q.asIdeal.quotientAtPrime p) =
      (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).height)

/- Map-quotient height equals `ringKrullDim` of the AtPrime localization of `A ⧸ q` at the
image of `p`, by `IsLocalization.AtPrime.ringKrullDim_eq_height`. -/
#check (IsLocalization.AtPrime.ringKrullDim_eq_height :
  ∀ {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime] (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization.AtPrime A I],
    ringKrullDim A = I.height)

/- Definition 111.18.1 (2): a topological space is catenary when every nested pair of
irreducible closed subsets admits a maximal chain of irreducible closed subsets, and every
such chain has the same finite length. -/
@[stacks 027O]
#check (TopologicalSpace.CatenarySpace : ∀ (X : Type u) [TopologicalSpace X], Prop)
