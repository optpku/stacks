/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.RingTheory.Depth
public import Mathlib.GroupTheory.Torsion

@[expose] public section

open AlgebraicGeometry.Scheme CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- For a Noetherian local ring of depth at least three and a regular element in its
maximal ideal, Picard pullback from the punctured spectrum to the punctured principal
quotient is injective on torsion classes. -/
theorem picardPullback_injective_on_torsion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) :
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := PuncturedSpectrum.puncturedOpen A
    Set.InjOn (Scheme.Hom.picardPullback (quotientMap ∣_ punctured))
      (AddCommGroup.torsion (Scheme.PicardGroup punctured.toScheme)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
