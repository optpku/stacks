/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Cokernel

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace ModuleValuedFunctor

/-- The categorical kernel of a morphism in the explicitly bundled category of
module-valued functors over a commutative ring. -/
def pointwiseKernel {A : CommRingCat.{u}}
    {F G : bundled.{u, u} A} (f : F ⟶ G) : bundled.{u, u} A :=
  @kernel _ _ (bundledHasZeroMorphisms A)
    F G f (@HasKernels.has_limit _ _ (bundledHasZeroMorphisms A)
      (bundledHasKernels A) F G f)

namespace Adequate

/-- Tensor adequacy is preserved by the categorical kernel of a morphism between
tensor-adequate module-valued functors. -/
theorem kernel {A : CommRingCat.{u}}
    {F G : bundled.{u, u} A} (φ : F ⟶ G)
    (hF : TensorAdequate F) (hG : TensorAdequate G) :
    TensorAdequate (pointwiseKernel φ) := sorry

end Adequate

end ModuleValuedFunctor
