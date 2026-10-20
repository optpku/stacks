module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.BaseChange
import StacksCheckRecall

/-!
# Base change of integral and finite morphisms of algebraic spaces

The base change of an integral (resp. finite) morphism of algebraic spaces by
any morphism of algebraic spaces is again integral (resp. finite).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.45.5 (1): The base change of an integral morphism of algebraic
spaces is integral. -/
@[stacks 03ZS] #check
  (AlgebraicGeometry.AlgebraicSpace.isIntegralHom_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}},
      MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.IsIntegralHom S :
          MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

/- Lemma 67.45.5 (2): The base change of a finite morphism of algebraic spaces
is finite. -/
@[stacks 03ZS] #check
  (AlgebraicGeometry.AlgebraicSpace.isFinite_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}},
      MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.IsFinite S :
          MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
