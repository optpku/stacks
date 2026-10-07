module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import stacks_project.Chap61.Lemma_61_5_3_Ring

/-!
# Universal property of w-localization

The constructed algebra map `A → A_w` is universal among maps into rings whose
prime spectra are w-local: such a map factors uniquely through a w-local map of
spectra.
-/

@[expose] public section

universe u v

open PrimeSpectrum

namespace Algebra.WLocalHull

variable {A : Type u} [CommRing A]

/-- Lemma 61.5.5 (Universal property of the construction):
let `A` be a ring, and let `algebraMap A (wLocalization A)` be the ring map
constructed in Lemma 61.5.3. For any ring map `f : A →+* B` such that
`PrimeSpectrum B` is w-local, there is a unique factorization
`g : wLocalization A →+* B` of `f` through `algebraMap A (wLocalization A)`
such that `comap g` is w-local. -/
@[stacks 0977]
theorem existsUnique_hom {B : Type v} [CommRing B] (f : A →+* B)
    [WLocalSpace (PrimeSpectrum B)] :
    ∃! g : wLocalization A →+* B,
      g.comp (algebraMap A (wLocalization A)) = f ∧ IsWLocalMap (comap g) :=
  sorry

/-- Two ring maps out of `wLocalization A` that agree after composing with
`algebraMap A (wLocalization A)` and induce w-local maps of spectra are equal. -/
theorem eq_of_isWLocalMap {B : Type v} [CommRing B]
    {g₁ g₂ : wLocalization A →+* B}
    (h : g₁.comp (algebraMap A (wLocalization A)) =
      g₂.comp (algebraMap A (wLocalization A)))
    [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap g₁)] [IsWLocalMap (comap g₂)] :
    g₁ = g₂ :=
  sorry

/-- The universal property of `wLocalization A`, with the given map `A → B`
packaged as an `A`-algebra structure on `B`. -/
theorem existsUnique_algHom {B : Type v} [CommRing B] [Algebra A B]
    [WLocalSpace (PrimeSpectrum B)] :
    ∃! g : wLocalization A →ₐ[A] B, IsWLocalMap (comap g.toRingHom) :=
  sorry

end Algebra.WLocalHull
