module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.Quotient

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.tower :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ),
    SequentialInverseSystem (ModuleCat A))
