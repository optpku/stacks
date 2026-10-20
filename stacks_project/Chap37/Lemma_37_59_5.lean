/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.AffineSpace.StandardZariskiCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace RingedSpace
namespace ModuleDerived
namespace IsMPseudoCoherent

/- Lemma 37.59.5: for a finite type morphism of affine schemes `f : X ⟶ S`, the
affine-space pushforward criterion for `E` in degree `m` holds globally if and only if it
holds for the restriction of `E` to every member of a chosen standard Zariski cover of `X`. -/
@[stacks 09VE] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.exists_affineSpace_pushforward_iff_standardZariskiCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]
      [Scheme.Hom.FiniteType f] (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ)
      (𝒰 : X.StandardZariskiCover.{u, v}),
      (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f ∧
          IsMPseudoCoherent
            ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m) ↔
        ∀ j : 𝒰.index,
          ∃ (n : ℕ) (i : 𝒰.X j ⟶ AffineSpace (ULift.{u} (Fin n)) S),
            IsClosedImmersion i ∧
              i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = 𝒰.f j ≫ f ∧
              IsMPseudoCoherent
                ((RingedSpace.moduleDerivedPushforward i.toShHom).obj
                  ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace
                    (𝒰.opens j)).obj E)) m)

end IsMPseudoCoherent
end ModuleDerived
end RingedSpace
end AlgebraicGeometry
