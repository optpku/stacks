module

import StacksCheckRecall

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.RingTheory.Spectrum.Prime.AffinePlane

@[expose] public section

universe u

noncomputable section

open PrimeSpectrum

/- Exercise 111.6.30 (1) -/
@[stacks 02DJ] #check
  (MvPolynomial.AffinePlane.prime_eq_bot_or_span_or_point :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      (p : PrimeSpectrum (MvPolynomial (Fin 2) k)) →
        p.asIdeal = ⊥ ∨
          (∃ f : MvPolynomial (Fin 2) k, Irreducible f ∧ p.asIdeal = Ideal.span {f}) ∨
            ∃ x : Fin 2 → k, p = MvPolynomial.pointToPoint x)

/- Exercise 111.6.30 (2) -/
@[stacks 02DJ] #check
  (MvPolynomial.AffinePlane.mem_closedPoints_iff :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {p : PrimeSpectrum (MvPolynomial (Fin 2) k)},
      p ∈ closedPoints (PrimeSpectrum (MvPolynomial (Fin 2) k)) ↔
        ∃ x : Fin 2 → k, p = MvPolynomial.pointToPoint x)

/- Maximal ideals of `k[x, y]` are vanishing ideals of points. -/
#check MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton

/- Localization realizes the generic fiber: the range of `Spec(S⁻¹R) → Spec R` is
`{p | Disjoint S p.asIdeal}`. -/
#check PrimeSpectrum.localization_comap_range

/- Specialization on `Spec` is inclusion of primes. -/
#check PrimeSpectrum.le_iff_specializes

/- Closed points of `Spec` are maximal ideals. -/
#check PrimeSpectrum.isClosed_singleton_iff_isMaximal

/- Coordinates `Fin 2 → k` are pairs `k × k`. -/
#check piFinTwoEquiv

/- Scheme-level reason for the name affine 2-space. -/
#check AlgebraicGeometry.AffineSpace.SpecIso
