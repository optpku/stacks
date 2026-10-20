module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
import StacksCheckRecall

/-!
# Composition of finite locally free morphisms of algebraic spaces

The composition of a pair of finite locally free morphisms of algebraic spaces
is finite locally free.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.46.4: The composition of finite locally free morphisms of algebraic
spaces is finite locally free. -/
@[stacks 03ZX] #check
  (AlgebraicGeometry.AlgebraicSpace.finiteLocallyFree_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree S :
        MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.finiteLocallyFree_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree f]
    [AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree g],
    AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
