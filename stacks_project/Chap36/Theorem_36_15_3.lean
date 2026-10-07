module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

universe u

/- Theorem 36.15.3: every quasi-compact quasi-separated scheme has a perfect object whose
integral shifts detect zero objects in the derived category with quasicoherent cohomology. -/
@[stacks 09IS] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_isPerfect_isWeakGenerator :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
      ∃ P : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X,
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect P.obj ∧
          CategoryTheory.IsWeakGenerator P)
