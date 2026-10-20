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
