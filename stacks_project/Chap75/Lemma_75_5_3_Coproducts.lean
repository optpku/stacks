module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Coproduct

universe u

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.hasCoproducts :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.Limits.HasCoproducts.{u} (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.inclusionPreservesCoproducts :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S) (I : Type u),
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I)
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.inclusion X))
