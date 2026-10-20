module

import StacksCheckRecall

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Composition

/-!
# Composition of flat morphisms of algebraic spaces

The composition of a pair of flat morphisms of algebraic spaces is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.30.3: The composition of flat morphisms is flat. -/
@[stacks 03MN] #check (AlgebraicGeometry.AlgebraicSpace.flat_comp :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y Z : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.Flat f] [AlgebraicGeometry.AlgebraicSpace.Flat g],
    AlgebraicGeometry.AlgebraicSpace.Flat (f ≫ g))
