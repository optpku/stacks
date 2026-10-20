/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.RingTheory.Pullback.LocalizationAway
import Mathlib.Tactic.CrossRefAttribute

/-!
# Open immersions induced by cartesian squares of rings

This file relates cartesian squares of commutative rings to open immersions obtained by
restricting morphisms between affine spectra.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace CategoryTheory.IsPullback

/-- Let a cartesian square of commutative rings be given. If an open of one affine spectrum is
a finite union of basic opens whose defining elements come from the opposite ring, and the
corresponding canonical localization maps are bijective, then its induced map into the spectrum
of the pullback ring is an open immersion. -/
@[stacks 01Z9]
theorem isOpenImmersion_restrictSpecMap_of_basicOpenCover
    {B R R' B' : Type u} [CommRing B] [CommRing R] [CommRing R'] [CommRing B']
    (s : B →+* R) (t : R' →+* R) (left : B' →+* B) (right : B' →+* R')
    (hcart : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t))
    {n : ℕ} (W' : (Spec (of R')).Opens) (f : Fin n → R') (g : Fin n → B)
    (hW' : W' = ⨆ i, PrimeSpectrum.basicOpen (f i))
    (hfg : ∀ i, t (f i) = s (g i))
    (hlocal : ∀ i, Function.Bijective (Localization.awayMap s (g i))) :
    IsOpenImmersion (W'.ι ≫ Spec.map (ofHom right)) := sorry

end CategoryTheory.IsPullback
