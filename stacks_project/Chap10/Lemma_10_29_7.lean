/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import ReasLib.RingTheory.Spectrum.Prime.BasicOpen.Image
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.29.7 (Tag 00FB): the polynomial structure map has compact-open images.

@stack 00FB
-/

open Polynomial PrimeSpectrum

universe u

section

variable {R : Type u} [CommRing R]

/-
Lemma 10.29.7: the exact image formula for a standard open under the structure morphism
`Spec(R[X]) → Spec(R)` is the canonical theorem `Polynomial.image_comap_C_basicOpen`.
-/
@[stacks 00FB "standard-open image"]
#check @Polynomial.image_comap_C_basicOpen

@[stacks 00FB "compact image of a principal basic open"]
#check @PrimeSpectrum.isCompact_image_comap_basicOpen

/- Together with compactness above, the canonical open-map theorem for
`Spec(R[X]) → Spec(R)` says that every standard-open image is quasi-compact open. -/
@[stacks 00FB "polynomial structure-map openness"]
#check @Polynomial.isOpenMap_comap_C

end
