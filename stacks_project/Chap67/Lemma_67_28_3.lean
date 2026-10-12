/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_3_Pullback

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

/-- Lemma 67.28.3 (1): The base change of a finite presentation morphism of
algebraic spaces is of finite presentation. -/
@[stacks 03XR]
instance finitePresentation_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 67.28.3 (2): The base change of a locally of finite presentation
morphism of algebraic spaces is locally of finite presentation. -/
@[stacks 03XR]
instance locallyOfFinitePresentation_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) :=
    sorry

#check FinitePresentation.of_isPullback
#check FinitePresentation.pullback_snd
#check LocallyOfFinitePresentation.of_isPullback
#check LocallyOfFinitePresentation.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
