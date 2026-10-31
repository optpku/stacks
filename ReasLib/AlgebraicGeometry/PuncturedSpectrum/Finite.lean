/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.RingTheory.Depth

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite scheme over the spectrum of a Noetherian local ring whose
closed-point stalks have depth at least two is isomorphic to the spectrum of
its section ring over the inverse image of the punctured spectrum.
The identification uses the canonical restriction from global sections to that open set. -/
theorem isSpec_of_finite_puncturedDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (pi : Y ⟶ Spec (CommRingCat.of A)) [IsFinite pi]
    (hdepth : ∀ y : Y, y ∈ closedPoints Y →
      (2 : ℕ∞) ≤ moduleDepth (Y.presheaf.stalk y) (Y.presheaf.stalk y)) :
    let U : (Spec (CommRingCat.of A)).Opens := PuncturedSpectrum.puncturedOpen A
    IsIso Y.toSpecΓ ∧
      IsIso (Y.presheaf.map (homOfLE (show pi ⁻¹ᵁ U ≤ ⊤ from le_top)).op) := sorry

end AlgebraicGeometry.Scheme.Hom
