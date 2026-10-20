module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.FormallyUnramified
import StacksCheckRecall

/-!
# Universal first-order thickenings of formally unramified morphisms

If `Z ⟶ X` is formally unramified, then the ambient map of a universal
first-order thickening of `Z` over `X` is formally unramified.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.15.7: Let `S` be a scheme. Let `Z ⟶ X` be a formally unramified
morphism of algebraic spaces over `S`. Then the universal first-order
thickening `Z'` is formally unramified over `X`. -/
@[stacks 0609] #check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.formallyUnramified :
    ∀ {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S} (i : Z ⟶ Z') (f : Z' ⟶ X)
      [AlgebraicSpace.IsUniversalFirstOrder i f]
      [AlgebraicSpace.FormallyUnramified (i ≫ f)],
      AlgebraicSpace.FormallyUnramified f)
