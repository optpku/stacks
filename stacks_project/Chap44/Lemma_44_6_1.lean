/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Curve

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativePicard

/- Lemma 44.6.1 -/
@[stacks 0B9U] #check
  (AlgebraicGeometry.RelativePicard.smoothProjectiveCurve_picardHypotheses :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [Smooth X.hom] [Projective X.hom],
      SchemeOverField.BaseField.hasRationalPoint X →
      ∃ σ : Spec (CommRingCat.of k) ⟶ X.left,
        σ ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) ∧
          ∀ T : SchemeOverField k,
            IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
              (pullback.fst T.hom X.hom).toShHom))

end AlgebraicGeometry.RelativePicard
