/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.FMapHom
import StacksCheckRecall

/-!
# Lemma 66.18.10

Canonical bijections between morphisms into small étale pushforward, morphisms out of small
étale inverse image, and `f`-maps of sheaves of sets.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.18.10: Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.
For sheaves of sets `𝒢` on `Y_étale` and `ℱ` on `X_étale`, maps `𝒢 ⟶ f_small,* ℱ`,
maps `f_small⁻¹ 𝒢 ⟶ ℱ`, and `f`-maps from `𝒢` to `ℱ` are canonically bijective. -/
@[stacks 03G4] #check (AlgebraicGeometry.AlgebraicSpace.fMapHomEquiv :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    (𝒢 ⟶ (sheafPushforwardType f).obj ℱ) ≃ FMap f 𝒢 ℱ)

#check (AlgebraicGeometry.AlgebraicSpace.fMapInverseImageHomEquiv :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    ((sheafTypeInverseImage f).obj 𝒢 ⟶ ℱ) ≃ FMap f 𝒢 ℱ)
