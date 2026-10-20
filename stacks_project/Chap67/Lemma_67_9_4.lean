module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Composition
import StacksCheckRecall

/-!
# Composition of closed morphisms of algebraic spaces

The composition of a pair of closed morphisms of algebraic spaces is closed,
and the composition of a pair of universally closed morphisms of algebraic
spaces is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.9.4 (1): The composition of closed morphisms of algebraic spaces is closed. -/
@[stacks 03IU] #check
  (AlgebraicGeometry.AlgebraicSpace.closed_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.Closed S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 67.9.4 (2): The composition of universally closed morphisms of algebraic spaces
is universally closed. -/
@[stacks 03IU] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyClosed_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.UniversallyClosed S :
        MorphismProperty (AlgebraicSpace S)))
