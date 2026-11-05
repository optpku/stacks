/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Restriction
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Underlying

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/-- The full category of adequate module-valued functors on `Alg_A`, using the
canonical tensor-extension functor. -/
abbrev Adeq (A : CommRingCat.{u}) := TensorAdeq A

/-- Every object of `Adeq A` is adequate. -/
theorem Adeq.adequate {A : CommRingCat.{u}} (F : Adeq A) :
    TensorAdequate F.obj := F.property

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
