module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Kernel
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.BaseChange
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.BaseChangeMaps

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable {A A' : CommRingCat.{u}}

namespace ModuleValuedFunctor

namespace Adequate

/-- Tensor adequacy descends along `f : A ⟶ A'` when the restricted functor is
adequate and the canonical two-step base-change sequence is objectwise injective
and exact. -/
theorem of_baseChange_exact
    (f : A ⟶ A') (F : bundled.{u, u} A)
    (hF' : TensorAdequate ((restrictAlong f).obj F))
    (h_injective : ∀ B, Function.Injective ((Under.baseChangeUnit f F.toFunctor).app B))
    (h_exact : ∀ B, Function.Exact ((Under.baseChangeUnit f F.toFunctor).app B)
      ((Under.baseChangeDifferential f F.toFunctor).app B)) :
    TensorAdequate F := sorry

end Adequate

end ModuleValuedFunctor
