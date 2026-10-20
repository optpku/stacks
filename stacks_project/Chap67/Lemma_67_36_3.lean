module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.BaseChange
import StacksCheckRecall

/-!
# Base change of syntomic morphisms of algebraic spaces

The base change of a syntomic morphism of algebraic spaces by any morphism of
algebraic spaces is again a syntomic morphism.
-/

@[expose] public section

universe u

/- Lemma 67.36.3: The base change of a syntomic morphism is syntomic. -/
@[stacks 03Z9] #check
  (AlgebraicGeometry.AlgebraicSpace.syntomic_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.Syntomic S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
