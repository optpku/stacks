module

public import stacks_project.Chap67.Lemma_67_28_3_Pullback
import StacksCheckRecall

/-!
# Base change of finite-presentation morphisms of algebraic spaces

The base change of a finite-presentation morphism of algebraic spaces by any
morphism of algebraic spaces is again of finite presentation. The same holds
for morphisms locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.28.3: A base change of a morphism of finite presentation is of
finite presentation. The same holds for locally of finite presentation. -/
@[stacks 03XR] #check
  (AlgebraicGeometry.AlgebraicSpace.finitePresentation_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
