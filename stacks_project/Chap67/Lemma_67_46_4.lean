module

public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of finite locally free morphisms of algebraic spaces

The composition of a pair of finite locally free morphisms of algebraic spaces
is finite locally free.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.46.4: The composition of finite locally free morphisms of algebraic
spaces is finite locally free. -/
@[stacks 03ZX]
instance finiteLocallyFree_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of finite locally free morphisms of algebraic spaces is
finite locally free. -/
instance finiteLocallyFree_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteLocallyFree f] [FiniteLocallyFree g] :
    FiniteLocallyFree (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
