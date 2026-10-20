module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

/- Lemma 76.15.9: Universal first-order thickenings are preserved by cartesian
base change of the closed and ambient algebraic spaces. -/
@[stacks 060B]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (f' : Z' ⟶ W') (closedSq : CommSq f iZ iW f')
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
    (rightSq : IsPullback f' fZ fW g) [IsUniversalFirstOrder iW fW],
    IsUniversalFirstOrder iZ fZ)
