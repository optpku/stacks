module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
import StacksCheckRecall

/-!
# Base change of universal homeomorphisms of algebraic spaces

The base change of a universal homeomorphism of algebraic spaces by any morphism
of algebraic spaces is again a universal homeomorphism.
-/

universe u

/- Lemma 67.53.4: The base change of a universal homeomorphism of algebraic spaces by
any morphism of algebraic spaces is a universal homeomorphism. -/
@[stacks 0CFT] #check
  (AlgebraicGeometry.AlgebraicSpace.universalHomeomorphism_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
