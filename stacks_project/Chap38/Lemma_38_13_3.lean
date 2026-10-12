/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.TensorPullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.13.3: a point `x` is weakly associated to the tensor product of a finite-type
quasicoherent module `ℱ`, flat over the base at `x`, with the pullback of a quasicoherent
module `𝒢` exactly when `f x` is weakly associated to `𝒢` and `f.asFiber x` is associated
to the restriction of `ℱ` to the fiber over `f x`. -/
@[stacks 05IH]
#check
  (AlgebraicGeometry.Scheme.Modules.mem_weakAss_tensor_pullback_iff_of_flatOverAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (x : X),
      flatOverAt ℱ f x →
        (x ∈ (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢).weakAss ↔
          f x ∈ 𝒢.weakAss ∧
            f.asFiber x ∈
              ((Scheme.Modules.pullback (f.fiberι (f x))).obj ℱ).associatedPoints))

end AlgebraicGeometry.Scheme.Modules
