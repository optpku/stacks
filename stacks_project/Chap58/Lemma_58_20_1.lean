/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Finite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry ENat

universe u

/- Lemma 58.20.1: for a finite morphism from a scheme to the spectrum of a
Noetherian local ring, if every closed-point stalk has depth at least two, then
the source is the spectrum of the section ring over the inverse image of the
punctured spectrum. -/
@[stacks 0BM8] #check (AlgebraicGeometry.Scheme.Hom.isSpec_of_finite_puncturedDepth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (pi : Y ⟶ Spec (CommRingCat.of A)) [IsFinite pi]
    (hdepth : ∀ y : Y, y ∈ closedPoints Y →
      (2 : ℕ∞) ≤ moduleDepth (Y.presheaf.stalk y) (Y.presheaf.stalk y)),
    let U : (Spec (CommRingCat.of A)).Opens := PuncturedSpectrum.puncturedOpen A
    IsIso Y.toSpecΓ ∧
      IsIso (Y.presheaf.map (homOfLE (show pi ⁻¹ᵁ U ≤ ⊤ from le_top)).op))
