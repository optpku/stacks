module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pointCohomologyMap :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') (i : ℤ),
    (ModuleCat.extendScalars (pointTensorMap g' f' f g h_comm xbar').hom).obj
        (pointBaseChangeHomology g' f' f g h_comm K xbar' i) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat (etaleLocalRing X' xbar')) i).obj
        (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K')))
