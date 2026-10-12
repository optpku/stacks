/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.BaseField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativePicard

/-- A smooth projective curve over a field with a rational point has a section
and universally trivial structure-sheaf pushforward after base change. -/
theorem smoothProjectiveCurve_picardHypotheses
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom]
    (h_point : SchemeOverField.BaseField.hasRationalPoint X) :
    ∃ σ : Spec (CommRingCat.of k) ⟶ X.left,
      σ ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) ∧
        ∀ T : SchemeOverField k,
          IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
            (pullback.fst T.hom X.hom).toShHom) := sorry

end AlgebraicGeometry.RelativePicard
