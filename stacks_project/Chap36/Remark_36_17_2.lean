module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Remark 36.17.2 (1): a quasi-compact and quasi-separated scheme admits a perfect weak
generator of `DerivedQCoh X`. -/
@[stacks 0GEF] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_isPerfect_isWeakGenerator :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
      ∃ G : AlgebraicGeometry.Scheme.DerivedQCoh X,
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect G.obj ∧
          CategoryTheory.IsWeakGenerator G)

/- Remark 36.17.2 (2): every perfect weak generator of `DerivedQCoh X` classically generates
its compact, equivalently perfect, objects. -/
@[stacks 0GEF] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.isClassicalGeneratorOfCompacts :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (G : AlgebraicGeometry.Scheme.DerivedQCoh X),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect G.obj →
        CategoryTheory.IsWeakGenerator G →
          CategoryTheory.IsClassicalGeneratorOfCompacts G)

end AlgebraicGeometry.Scheme.DerivedQCoh
