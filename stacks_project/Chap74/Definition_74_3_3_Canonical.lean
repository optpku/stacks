module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData.Canonical

@[expose] public section

open CategoryTheory

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.canonicalFunctor :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X),
    AlgebraicGeometry.AlgebraicSpace.QCoh X ⥤
      AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Xᵢ f)
