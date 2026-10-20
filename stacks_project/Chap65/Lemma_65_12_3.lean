module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange

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

/- Lemma 65.12.3 (1): a base change of an immersion of algebraic spaces
is again an immersion. -/
@[stacks 02YW] #check (AlgebraicGeometry.AlgebraicSpace.isImmersion_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@IsImmersion S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 65.12.3 (2): a base change of a closed immersion of algebraic spaces
is again a closed immersion. -/
@[stacks 02YW] #check (AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 65.12.3 (3): a base change of an open immersion of algebraic spaces
is again an open immersion. -/
@[stacks 02YW] #check (AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
