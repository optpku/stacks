module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.QuasiFinite
public import ReasLib.RingTheory.KrullDimension.Relative.Transport

@[expose] public section

/-!
# Relative dimension and quasi-finite polynomial charts

This leaf records the reusable bridge from relative dimension to quasi-finite
polynomial presentations. It also exposes the pointwise and whole-fiber
dimension bounds supplied by a quasi-finite polynomial algebra structure.

@stack 00QE
@stack 00QG
-/

noncomputable section

universe u v

namespace Algebra.QuasiFinite

variable {R : Type u} [CommRing R]

/-- A quasi-finite algebra over an `m`-variable polynomial algebra over `R` has fibers over `R`
of Krull dimension at most `m`. -/
@[stacks 00QG "fiber dimension bound for a quasi-finite polynomial algebra"]
theorem fiberKrullDim_le_of_mvPolynomial
    {A : Type v} [CommRing A] [Algebra R A] {m : ℕ}
    [Algebra (MvPolynomial (Fin m) R) A]
    [IsScalarTower R (MvPolynomial (Fin m) R) A]
    [Algebra.FiniteType R A] [Algebra.QuasiFinite (MvPolynomial (Fin m) R) A]
    (p : PrimeSpectrum R) :
    ringKrullDim (p.asIdeal.Fiber A) ≤ (m : WithBot ℕ∞) := sorry

/-- A quasi-finite algebra over an `m`-variable polynomial algebra over `R` has relative
dimension at most `m` at every target prime. -/
@[stacks 00QG "relative dimension bound for a quasi-finite polynomial algebra"]
theorem relativeDimensionAt_le_of_mvPolynomial
    {A : Type v} [CommRing A] [Algebra R A] {m : ℕ}
    [Algebra (MvPolynomial (Fin m) R) A]
    [IsScalarTower R (MvPolynomial (Fin m) R) A]
    [Algebra.FiniteType R A] [Algebra.QuasiFinite (MvPolynomial (Fin m) R) A]
    (q : PrimeSpectrum A) :
    relativeDimensionAt R A q ≤ (m : WithBot ℕ∞) := sorry

/-- A finite-type algebra over a field which is quasi-finite over an `m`-variable polynomial
algebra has Krull dimension at most `m`. -/
@[stacks 00QG "global dimension bound over a field"]
theorem ringKrullDim_le_of_mvPolynomial
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] {m : ℕ}
    [Algebra (MvPolynomial (Fin m) k) A]
    [IsScalarTower k (MvPolynomial (Fin m) k) A]
    [Algebra.FiniteType k A] [Algebra.QuasiFinite (MvPolynomial (Fin m) k) A] :
    ringKrullDim A ≤ (m : WithBot ℕ∞) := sorry

end Algebra.QuasiFinite

namespace RelativeDimensionAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- At a point where the relative dimension is `n`, a finite-type `R`-algebra admits a
principal localization which is quasi-finite over an `n`-variable polynomial algebra over
`R`. -/
@[stacks 00QE "quasi-finite polynomial localization from relative dimension"]
theorem exists_quasiFinite_polynomial_localizationAway
    [Algebra.FiniteType R S] (n : ℕ) (q : PrimeSpectrum S)
    (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        RingHom.QuasiFinite φ.toRingHom := sorry

end RelativeDimensionAt
