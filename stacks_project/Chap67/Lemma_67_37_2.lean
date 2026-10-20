module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Composition
import StacksCheckRecall

/-!
# Composition of smooth morphisms of algebraic spaces

The composition of a pair of smooth morphisms of algebraic spaces is
smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.37.2: The composition of smooth morphisms is smooth. -/
@[stacks 03ZD] #check
  (AlgebraicGeometry.AlgebraicSpace.smooth_isStableUnderComposition :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.AlgebraicSpace.Smooth S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.smooth_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.Smooth f]
    [AlgebraicGeometry.AlgebraicSpace.Smooth g],
    AlgebraicGeometry.AlgebraicSpace.Smooth (f ≫ g))
