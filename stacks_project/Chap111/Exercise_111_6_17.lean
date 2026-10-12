/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import ReasLib.RingTheory.Spectrum.Prime.Artinian
public import ReasLib.RingTheory.MvPolynomial.SquareZero.Noetherian
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

/- Exercise 111.6.17: Noetherian rings have Noetherian spectra, but the converse is false.
The rational polynomial ring in positive-natural-number variables modulo the ideal generated
by the individual variable squares has Noetherian spectrum and is not a Noetherian ring. -/
@[stacks 02D9] #check (MvPolynomial.SquareZero.not_isNoetherianRing :
  ¬ IsNoetherianRing (MvPolynomial.SquareZero.Quotient (σ := ℕ+) (k := ℚ)))

section

variable {R : Type u} [CommSemiring R] [IsNoetherianRing R]

/- Companion: a Noetherian commutative semiring has Noetherian prime spectrum. -/
#check (PrimeSpectrum.instNoetherianSpace R : NoetherianSpace (PrimeSpectrum R))

end

/- Companion: the counterexample has Noetherian spectrum. -/
#check (MvPolynomial.SquareZero.instNoetherianSpace :
  NoetherianSpace (PrimeSpectrum (MvPolynomial.SquareZero.Quotient (σ := ℕ+) (k := ℚ))))

section

variable {R : Type u} [CommSemiring R] [IsArtinianRing R]

/- Companion: an Artinian commutative semiring has Artinian prime spectrum. -/
#check (PrimeSpectrum.instArtinianSpace : ArtinianSpace (PrimeSpectrum R))

end

/- Companion: the same counterexample has Artinian spectrum. -/
#check (MvPolynomial.SquareZero.instArtinianSpace :
  ArtinianSpace (PrimeSpectrum (MvPolynomial.SquareZero.Quotient (σ := ℕ+) (k := ℚ))))

section

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/- Companion: an Artinian ring has finite prime spectrum. -/
#check (inferInstance : Finite (PrimeSpectrum R))

/- Companion: an Artinian ring has discrete prime spectrum. -/
#check (inferInstance : DiscreteTopology (PrimeSpectrum R))

/- Companion: Hopkins–Levitzki, so a non-Noetherian ring is not Artinian. -/
#check (inferInstance : IsNoetherianRing R)

end

section

variable {X : Type u} [TopologicalSpace X] [Finite X]

/- Companion: finite spaces are Artinian. -/
#check (TopologicalSpace.Finite.to_artinianSpace : ArtinianSpace X)

end

/- Companion: the square-zero quotient is local over a local coefficient ring. -/
#check (MvPolynomial.SquareZero.quotient_isLocalRing :
  IsLocalRing (MvPolynomial.SquareZero.Quotient (σ := ℕ+) (k := ℚ)))

/- Companion: over a field the maximal ideal of the square-zero quotient is locally nilpotent. -/
#check (MvPolynomial.SquareZero.maximalIdeal_isLocallyNilpotent :
  (IsLocalRing.maximalIdeal
    (MvPolynomial.SquareZero.Quotient (σ := ℕ+) (k := ℚ))).IsLocallyNilpotent)

/- Companion: with infinitely many variables, a nonzero class remains nonzero after multiplying
by a fresh generator. -/
#check (MvPolynomial.SquareZero.exists_generator_mul_ne_zero :
  ∀ {x : MvPolynomial.SquareZero.Quotient (σ := ℕ+) (k := ℚ)}, x ≠ 0 →
    ∃ index : ℕ+, MvPolynomial.SquareZero.generator index * x ≠ 0)
