/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_46_5_Pullback

/-!
# Base change of finite locally free morphisms of algebraic spaces

The base change of a finite locally free morphism of algebraic spaces by any
morphism of algebraic spaces is again a finite locally free morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.46.5: The base change of a finite locally free morphism is finite
locally free. -/
@[stacks 03ZY]
instance finiteLocallyFree_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S)) := sorry

#check FiniteLocallyFree.of_isPullback
#check FiniteLocallyFree.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
