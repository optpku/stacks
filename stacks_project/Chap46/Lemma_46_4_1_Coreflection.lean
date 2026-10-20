module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap46.Remark_46_3_15_AdequateCategory

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor.Adequate

/-- The inclusion of adequate module-valued functors on `Alg_A` has a right adjoint. -/
instance inclusionIsLeftAdjoint (A : CommRingCat.{u}) :
    (ObjectProperty.ι (Adequate (tensorExtension A))).IsLeftAdjoint := sorry

end ModuleValuedFunctor.Adequate
