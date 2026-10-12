/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Kernel
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/- Lemma 46.3.11: for a morphism between adequate module-valued functors on
`Alg_A`, its kernel is adequate. -/
@[stacks 06V3] #check
  (ModuleValuedFunctor.Adequate.kernel :
    ∀ {A : CommRingCat.{u}}
      {F G : ModuleValuedFunctor.bundled.{u, u} A} (φ : F ⟶ G),
      ModuleValuedFunctor.TensorAdequate F →
        ModuleValuedFunctor.TensorAdequate G →
          ModuleValuedFunctor.TensorAdequate
            (ModuleValuedFunctor.pointwiseKernel φ))

end ModuleValuedFunctor
