module

public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import ReasLib.RingTheory.Spectrum.Prime.BasicOpen
public import ReasLib.RingTheory.Spectrum.Prime.Polynomial.BasicOpen
import StacksCheckRecall

@[expose] public section

open Polynomial PrimeSpectrum

universe u

/-
Exercise 111.24.3: for a commutative ring `A` and `f : A[X]`, the image of the principal
basic open `basicOpen f` under `comap C : PrimeSpectrum A[X] → PrimeSpectrum A` is
`⋃ i, basicOpen (f.coeff i)`. For a presentation with finitely many displayed
coefficients, all coefficients beyond its degree vanish and their basic opens are empty.
-/
@[stacks 0FKE] #check (Polynomial.image_comap_C_basicOpen_eq_iUnion :
  ∀ {A : Type u} [CommRing A] (f : A[X]),
    PrimeSpectrum.comap Polynomial.C ''
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A[X])) =
      ⋃ i : ℕ, (PrimeSpectrum.basicOpen (f.coeff i) : Set (PrimeSpectrum A)))

/- Pointwise, a prime lies in the image of `basicOpen f` iff some coefficient avoids it. -/
#check (Polynomial.mem_image_comap_C_basicOpen :
  ∀ {A : Type u} [CommRing A] (f : A[X]) (x : PrimeSpectrum A),
    x ∈ comap C '' basicOpen f ↔ ∃ i, f.coeff i ∉ x.asIdeal)
