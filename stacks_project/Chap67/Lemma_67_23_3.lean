module

public import stacks_project.Chap67.Lemma_67_23_3_Pullback

/-!
# Base change of finite-type morphisms of algebraic spaces

The base change of a finite-type morphism of algebraic spaces by any morphism
of algebraic spaces is again of finite type. The same holds for morphisms
locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.23.3 (1): The base change of a finite type morphism of algebraic
spaces is finite type. -/
@[stacks 03XH]
instance finiteType_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 67.23.3 (2): The base change of a locally of finite type morphism of
algebraic spaces is locally of finite type. -/
@[stacks 03XH]
instance locallyOfFiniteType_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

#check FiniteType.of_isPullback
#check FiniteType.pullback_snd
#check LocallyOfFiniteType.of_isPullback
#check LocallyOfFiniteType.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
