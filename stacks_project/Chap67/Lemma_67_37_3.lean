/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_3_Pullback

/-!
# Base change of smooth morphisms of algebraic spaces

The base change of a smooth morphism of algebraic spaces by any morphism of
algebraic spaces is again a smooth morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.37.3: The base change of a smooth morphism is smooth. -/
@[stacks 03ZE]
instance smooth_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

#check Smooth.of_isPullback
#check Smooth.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
