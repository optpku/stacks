module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Presentation

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.preRelation :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.Scheme.PreRelation (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.cover k))
