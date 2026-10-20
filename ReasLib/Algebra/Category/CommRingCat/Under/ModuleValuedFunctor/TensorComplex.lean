module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Underlying
public import Mathlib.Algebra.Homology.Additive

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace ModuleValuedFunctor

/-- The underlying additive-group tensor-extension functor preserves zero morphisms. -/
instance tensorExtensionUnderlying_preservesZeroMorphisms (A : CommRingCat.{u}) :
    (tensorExtensionUnderlying A).PreservesZeroMorphisms := sorry

/-- Extension of scalars of a cochain complex, viewed as an additive-group-valued functor
on `A`-algebras. -/
def tensorComplex (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (Under A ⥤ AddCommGrpCat.{u}) ℤ :=
  ((tensorExtensionUnderlying A).mapHomologicalComplex (up ℤ)).obj M

/-- Each term of the tensor complex is the underlying additive group of the corresponding
extension-of-scalars module over `B.right`. -/
theorem tensorComplex_obj (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (degree : ℤ) (B : Under A) :
    ((tensorComplex A M).X degree).obj B =
      (forget₂ (ModuleCat.{u} B.right) AddCommGrpCat.{u}).obj
        ((ModuleCat.extendScalars B.hom.hom).obj (M.X degree)) := sorry

/-- The differential at an `A`-algebra is the underlying additive map of the
`B.right`-linear extension of the original differential. -/
theorem tensorComplex_d_app (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (sourceDegree targetDegree : ℤ) (B : Under A) :
    ((tensorComplex A M).d sourceDegree targetDegree).app B =
      (forget₂ (ModuleCat.{u} B.right) AddCommGrpCat.{u}).map
        ((ModuleCat.extendScalars B.hom.hom).map (M.d sourceDegree targetDegree)) := sorry

end ModuleValuedFunctor
