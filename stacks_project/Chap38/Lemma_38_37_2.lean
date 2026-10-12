/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 38.37.2 (1): containment of `X' \ E` in `W` is equivalent to containment
of the canonical strict-transform blowup `X''` in `W`. -/
@[stacks 0EV8] #check
  (AlgebraicGeometry.IsAlmostBlowupSquare.openComplement_contained_iff_strictTransform_contained :
    ∀ {X X' W : Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData)
      (i : W ⟶ X') [IsClosedImmersion i] [LocallyOfFinitePresentation i],
      IsAlmostBlowupSquare b I →
        (i.ker ≤ (I.comap b).openComplement.ι.ker ↔
          i.ker ≤ (strictTransformSnd b (I.comap b) (𝟙 X)).ker))

/- Lemma 38.37.2 (2): containment of the canonical strict-transform blowup `X''`
in `W` is equivalent to the induced square on `W` being an almost blowup square. -/
@[stacks 0EV8]
#check
  (AlgebraicGeometry.IsAlmostBlowupSquare.strictTransform_contained_iff_restrict :
    ∀ {X X' W : Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData)
      (i : W ⟶ X') [IsClosedImmersion i] [LocallyOfFinitePresentation i],
      IsAlmostBlowupSquare b I →
        (i.ker ≤ (strictTransformSnd b (I.comap b) (𝟙 X)).ker ↔
          IsAlmostBlowupSquare (i ≫ b) I))

end AlgebraicGeometry
