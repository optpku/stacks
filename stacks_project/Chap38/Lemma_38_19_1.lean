/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Injectivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace IsPureAlong

/- Lemma 38.19.1: for a finite-type quasicoherent module that is pure along the closed
fibre and flat over a local base, a morphism is monic exactly when its stalk maps are
injective at the associated points of that fibre. -/
@[stacks 05L8] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.mono_iff_stalk_injective_on_fiber_associatedPoints :
    ∀ {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] (f : X ⟶ S)
      [Scheme.Hom.FiniteType f] (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent]
      [ℱ.IsFiniteType] [𝒢.IsQuasicoherent] (s : S)
      (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
      (h_pure : ℱ.IsPureAlong f s) (h_flat : flatOver ℱ f) (φ : ℱ ⟶ 𝒢),
      (∀ x : f.fiber s,
        x ∈ ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ).associatedPoints →
          Function.Injective (RingedSpace.moduleStalkHom (f.fiberι s x) φ)) ↔
        Mono φ)

end IsPureAlong
end Modules
end Scheme
end AlgebraicGeometry
