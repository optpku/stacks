/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.WLocalHull.UniversalProperty
import StacksCheckRecall

/-!
# Universal property of w-localization

The constructed algebra map `A → A_w` is universal among maps into rings whose
prime spectra are w-local: such a map factors uniquely through a w-local map of
spectra.
-/

@[expose] public section

universe u v

open PrimeSpectrum Algebra.WLocalHull

/- Lemma 61.5.5 (Universal property of the construction):
let `A` be a ring, and let `algebraMap A (wLocalization A)` be the ring map
constructed in Lemma 61.5.3. Every ring map to a ring with w-local prime spectrum
factors uniquely through this map among maps inducing w-local maps of spectra. -/
@[stacks 0977] #check (Algebra.WLocalHull.existsUnique_hom :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B] (f : A →+* B)
    [WLocalSpace (PrimeSpectrum B)],
    ∃! g : wLocalization A →+* B,
      g.comp (algebraMap A (wLocalization A)) = f ∧ IsWLocalMap (comap g))

#check (Algebra.WLocalHull.eq_of_isWLocalMap :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    {g₁ g₂ : wLocalization A →+* B}
    (h : g₁.comp (algebraMap A (wLocalization A)) =
      g₂.comp (algebraMap A (wLocalization A)))
    [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap g₁)] [IsWLocalMap (comap g₂)],
    g₁ = g₂)

#check (Algebra.WLocalHull.existsUnique_algHom :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
    [WLocalSpace (PrimeSpectrum B)],
    ∃! g : wLocalization A →ₐ[A] B, IsWLocalMap (comap g.toRingHom))
