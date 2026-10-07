module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Affine

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

/- Lemma 36.10.7: the derived object associated to a complex of modules over an affine
scheme is perfect if and only if the original complex is perfect in the derived category. -/
@[stacks 08EB] #check
  (AlgebraicGeometry.tilde.isPerfect_iff :
    ∀ (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat A) ℤ),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) ↔
        DerivedCategory.IsPerfect (DerivedCategory.Q.obj M))
