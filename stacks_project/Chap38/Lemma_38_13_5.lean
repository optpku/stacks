module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.TensorPullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.13.5: the weakly associated points of the tensor product of a finite-type
quasicoherent module `ℱ`, flat over the base, with the pullback of a quasicoherent module `𝒢`
are the images of the associated points of the fibers of `ℱ` over the weakly associated points
of `𝒢`. -/
@[stacks 05IJ]
#check
  (AlgebraicGeometry.Scheme.Modules.weakAss_tensor_pullback_eq_iUnion_fiber_associatedPoints :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (h_flat : flatOver ℱ f),
      (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢).weakAss =
        ⋃ s ∈ 𝒢.weakAss,
          f.fiberι s '' ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ).associatedPoints)

end AlgebraicGeometry.Scheme.Modules
