module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange
import StacksCheckRecall

/-!
# Base change of proper morphisms of algebraic spaces

The base change of a proper morphism of algebraic spaces by any morphism of
algebraic spaces is again proper.
-/

@[expose] public section

universe u

/- Lemma 67.40.3: A base change of a proper morphism of algebraic spaces is
proper. -/
@[stacks 04WP] #check
  (AlgebraicGeometry.AlgebraicSpace.proper_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.Proper S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
