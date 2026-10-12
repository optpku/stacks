/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_9_3_UniversallyClosed

/-!
# Base change of universally closed morphisms of algebraic spaces

The base change of a universally closed morphism of algebraic spaces by any
morphism of algebraic spaces is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.9.3: The base change of a universally closed morphism of algebraic
spaces by any morphism of algebraic spaces is universally closed. -/
@[stacks 03IS]
instance universallyClosed_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversallyClosed S : MorphismProperty (AlgebraicSpace S)) := sorry

#check UniversallyClosed.of_isPullback

end AlgebraicGeometry.AlgebraicSpace
