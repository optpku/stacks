module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyPrincipal.Pullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 71.6.9: Let S be a scheme. Let f : X' ⟶ X be a morphism of algebraic
spaces over S. Let Z ⊂ X be a locally principal closed subspace. Then the inverse
image f⁻¹(Z) is a locally principal closed subspace of X'. -/
@[stacks 083X] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipal.inverseImageι :
    ∀ {S : Scheme.{u}} {X X' Z : AlgebraicSpace S} (f : X' ⟶ X) (i : Z ⟶ X)
      [IsLocallyPrincipal i],
      IsLocallyPrincipal (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i))
