/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
its section ring over the inverse image of the punctured spectrum. -/
theorem isSpec_of_finite_puncturedDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (pi : Y ⟶ Spec (CommRingCat.of A)) [IsFinite pi]
    (hdepth : ∀ y : Y, y ∈ closedPoints Y →
      (2 : ℕ∞) ≤ moduleDepth (Y.presheaf.stalk y) (Y.presheaf.stalk y)) :
    let U : (Spec (CommRingCat.of A)).Opens := PuncturedSpectrum.puncturedOpen A
    let B : CommRingCat := CommRingCat.of (Γ(Y, pi ⁻¹ᵁ U))
    Nonempty (Y ≅ Spec B) := sorry

end AlgebraicGeometry.Scheme.Hom
