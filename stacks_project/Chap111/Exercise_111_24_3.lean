/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import ReasLib.RingTheory.Spectrum.Prime.BasicOpen
import StacksCheckRecall

@[expose] public section

open Polynomial PrimeSpectrum

universe u

/-
Exercise 111.24.3: for a commutative ring `A` and `f : A[X]`, the image of the principal
basic open `basicOpen f` under `comap C : PrimeSpectrum A[X] → PrimeSpectrum A` equals
`(zeroLocus (Set.range f.coeff))ᶜ`. This is the union `⋃ i, basicOpen (f.coeff i)`,
recovered by `iUnion_basicOpen_eq_compl_zeroLocus_range`.
-/
@[stacks 0FKE] #check (Polynomial.image_comap_C_basicOpen :
  ∀ {A : Type u} [CommRing A] (f : A[X]),
    comap C '' (basicOpen f : Set (PrimeSpectrum A[X])) =
      (zeroLocus (Set.range f.coeff))ᶜ)

/- The complement form is the source union of principal basic opens of the coefficients. -/
#check fun {A : Type u} [CommRing A] (f : A[X]) ↦
  (iUnion_basicOpen_eq_compl_zeroLocus_range f.coeff :
    (⋃ i, (basicOpen (f.coeff i) : Set (PrimeSpectrum A))) =
      (zeroLocus (Set.range f.coeff))ᶜ)

/- Pointwise, a prime lies in the image of `basicOpen f` iff some coefficient avoids it. -/
#check (Polynomial.mem_image_comap_C_basicOpen :
  ∀ {A : Type u} [CommRing A] (f : A[X]) (x : PrimeSpectrum A),
    x ∈ comap C '' basicOpen f ↔ ∃ i, f.coeff i ∉ x.asIdeal)
