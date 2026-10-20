module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.AffineComparison

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme CategoryTheory.MonoidalCategory

universe u

#check (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.mulMap :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules)
    (p c n : ℕ) (h : c ≤ n),
    (tensorLeft (ModuleCat.of A (I ^ (n - c) : Ideal A))).obj
        (Hom.IdealPowerCohomology.stage I f F p c) ⟶
      Hom.IdealPowerCohomology.stage I f F p n)
