module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.DerivedGenerator
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator_mem :
  ∀ (A : Type u) [CommRing A] (n : ℕ),
    AlgebraicGeometry.Scheme.ModuleDerived.quasicoherentProperty
      (AlgebraicGeometry.ProjectiveSpace.scheme A n)
      ((DerivedCategory.singleFunctor
        (AlgebraicGeometry.ProjectiveSpace.scheme A n).Modules 0).obj
        (AlgebraicGeometry.ProjectiveSpace.beilinsonGenerator A n)))

#check (AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator :
  ∀ (A : Type u) [CommRing A] (n : ℕ),
    AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
      (AlgebraicGeometry.ProjectiveSpace.scheme A n))

#check (AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator_obj :
  ∀ (A : Type u) [CommRing A] (n : ℕ),
    (AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator A n).obj =
      (DerivedCategory.singleFunctor
        (AlgebraicGeometry.ProjectiveSpace.scheme A n).Modules 0).obj
        (AlgebraicGeometry.ProjectiveSpace.beilinsonGenerator A n))
