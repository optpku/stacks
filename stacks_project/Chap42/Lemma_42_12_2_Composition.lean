module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicCycle

#check (AlgebraicGeometry.AlgebraicCycle.map_comp_of_proper :
  ∀ {R : Type v} [Semiring R]
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (c : AlgebraicCycle X.left R),
    map g.left (Y.hom.relativeDimensionFunction δ) (Z.hom.relativeDimensionFunction δ)
        (map f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) c) =
      map (f.left ≫ g.left) (X.hom.relativeDimensionFunction δ)
        (Z.hom.relativeDimensionFunction δ) c)

end AlgebraicGeometry.AlgebraicCycle
