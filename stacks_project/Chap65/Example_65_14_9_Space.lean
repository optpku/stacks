module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.PointSpace

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.sheafOfPoints :
  ∀ (k : Type u) [Field k],
    CategoryTheory.Sheaf
      (AlgebraicGeometry.Scheme.fppfTopology.over (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.base k)) (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.spacePoints :
  ∀ (k : Type u) [Field k], Type u)
