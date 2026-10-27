/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.InfinitesimalLifting
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.20.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is locally Noetherian and `f` is
locally of finite type. Then smoothness of `f` is equivalent to the
infinitesimal lifting property against small extensions of Artinian local
rings whose bottom arrow `β` is of finite type. -/
@[stacks 0APP] #check
  (AlgebraicGeometry.AlgebraicSpace.smooth_iff_smallExtensionLifting :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsLocallyNoetherian Y] [LocallyOfFiniteType f],
      Smooth f ↔
        ∀ (B' B : Type u) [CommRing B'] [CommRing B]
          (π : B' →+* B) [π.IsSmallExtension]
          (σ : Spec (CommRingCat.of B') ⟶ S)
          (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
          (β : ofOver (Over.mk σ) ⟶ Y) [FiniteType β],
          CommSq α (ofOverSpecMap π σ) f β →
            ∃ γ : ofOver (Over.mk σ) ⟶ X,
              ofOverSpecMap π σ ≫ γ = α ∧ γ ≫ f = β)

end AlgebraicGeometry.AlgebraicSpace
