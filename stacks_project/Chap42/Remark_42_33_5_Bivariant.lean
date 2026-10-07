module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- The bivariant-class restriction API remains available through this compatibility module. -/
#check (AlgebraicGeometry.BivariantClass.restrict :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ),
    BivariantClass delta f p → BivariantClass delta f' p)
