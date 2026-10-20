module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Restriction
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Underlying

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/-- Adequacy of the underlying additive functor implies tensor adequacy of the
bundled module-valued functor. -/
theorem tensorAdequate_of_underlyingAdequate {A : CommRingCat.{u}}
    {F : bundled A}
    (hF :
    @_root_.Adequate A inferInstance (Under A ⥤ AddCommGrpCat.{u})
      inferInstance (inferInstance : HasZeroMorphisms (Under A ⥤ AddCommGrpCat.{u}))
      (inferInstance : HasKernels (Under A ⥤ AddCommGrpCat.{u}))
      (tensorExtensionUnderlying A) F.toFunctor) :
    TensorAdequate F := sorry

end ModuleValuedFunctor
