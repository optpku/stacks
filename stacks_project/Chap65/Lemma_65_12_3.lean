module

public import stacks_project.Chap65.Lemma_65_12_3_Pullback

/-!
# Base change of immersions of algebraic spaces

The base change of an immersion (resp. closed immersion, resp. open immersion)
of algebraic spaces over a scheme `S` is again an immersion (resp. closed,
resp. open immersion) of algebraic spaces over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 65.12.3 (1): the base change of an immersion of algebraic spaces is an
immersion. -/
@[stacks 02YW]
instance isImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 65.12.3 (2): the base change of a closed immersion of algebraic spaces
is a closed immersion. -/
@[stacks 02YW]
instance isClosedImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 65.12.3 (3): the base change of an open immersion of algebraic spaces
is an open immersion. -/
@[stacks 02YW]
instance isOpenImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S)) := sorry

#check IsImmersion.of_isPullback
#check IsImmersion.pullback_snd
#check IsClosedImmersion.of_isPullback
#check IsClosedImmersion.pullback_snd
#check IsOpenImmersion.of_isPullback
#check IsOpenImmersion.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
