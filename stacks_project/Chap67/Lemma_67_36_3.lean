/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_36_3_Pullback

/-!
# Base change of syntomic morphisms of algebraic spaces

The base change of a syntomic morphism of algebraic spaces by any morphism of
algebraic spaces is again a syntomic morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.36.3: The base change of a syntomic morphism is syntomic. -/
@[stacks 03Z9]
instance syntomic_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Syntomic S : MorphismProperty (AlgebraicSpace S)) := sorry

#check Syntomic.of_isPullback
#check Syntomic.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
