module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Height-one prime ideals
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Prime ideals of height one, bundled as points of the prime spectrum. -/
@[stacks 031T "height-one prime spectrum"]
abbrev HeightOne (R : Type u) [CommRing R] :=
  {p : PrimeSpectrum R // p.asIdeal.height = 1}

namespace HeightOne

variable {R : Type u} [CommRing R]

/-- The prime ideal underlying a height-one point. -/
@[stacks 031T "ideal underlying a height-one point"]
abbrev asIdeal (p : HeightOne R) : Ideal R :=
  p.1.asIdeal

/-- The ideal underlying a height-one point is prime. -/
instance (p : HeightOne R) : p.asIdeal.IsPrime :=
  p.1.isPrime

/-- The underlying ideal of a height-one point has height one. -/
@[simp, stacks 031T "height of a height-one point"]
theorem asIdeal_height (p : HeightOne R) : p.asIdeal.height = 1 :=
  p.2

/-- Height-one points are determined by their underlying ideals. -/
@[ext, stacks 031T "extensionality of height-one points"]
theorem ext {p q : HeightOne R} (h : p.asIdeal = q.asIdeal) : p = q :=
  Subtype.ext (PrimeSpectrum.ext h)

/-- The quotient by a height-one prime of a two-dimensional Noetherian local ring has
Krull dimension one. -/
theorem quotientKrullDim_eq_one {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (p : PrimeSpectrum.HeightOne A)
    (hdim : ringKrullDim A = 2) : ringKrullDim (A ⧸ p.asIdeal) = 1 := sorry

end HeightOne

end PrimeSpectrum

namespace IsLocalRing

/-- For every Noetherian local ring of positive Krull dimension and every
element of its maximal ideal, some prime containing that element has
one-dimensional localization. -/
@[stacks 0BJG]
theorem exists_prime_mem_zeroLocus_singleton_dim_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : 1 ≤ ringKrullDim A) (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) :
    ∃ p : PrimeSpectrum A,
      p ∈ PrimeSpectrum.zeroLocus ({f} : Set A) ∧
        ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := sorry

end IsLocalRing
