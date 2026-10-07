module

public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Base change of universal homeomorphisms of algebraic spaces

The base change of a universal homeomorphism of algebraic spaces by any morphism
of algebraic spaces is again a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.53.4: The base change of a universal homeomorphism of algebraic spaces by
any morphism of algebraic spaces is a universal homeomorphism. -/
@[stacks 0CFT]
instance universalHomeomorphism_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S)) := sorry

#check UniversalHomeomorphism.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
