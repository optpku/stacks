module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange

/-!
# Base change of separation axioms for morphisms of algebraic spaces

The base change of a separated, locally separated, or quasi-separated morphism
of algebraic spaces by any morphism of algebraic spaces is again separated,
locally separated, or quasi-separated, respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.4.4 -/
@[stacks 03KL] #check (AlgebraicGeometry.AlgebraicSpace.separated_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderBaseChange
      (@Separated S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.locallySeparated_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderBaseChange
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.quasiSeparated_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderBaseChange
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
