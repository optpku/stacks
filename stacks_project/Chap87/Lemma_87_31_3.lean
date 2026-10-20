module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper.BaseChange
import StacksCheckRecall

/-!
# Base change of proper morphisms of formal algebraic spaces

The base change of a proper morphism of formal algebraic spaces by any
morphism of formal algebraic spaces is again proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 87.31.3: Proper morphisms of formal algebraic spaces are preserved by
base change. -/
@[stacks 0GBT] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.proper_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.FormalAlgebraicSpace.Proper S :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)))
