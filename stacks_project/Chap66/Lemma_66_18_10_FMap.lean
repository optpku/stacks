/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.FMapHom

/-!
# Comparison of `f`-maps with small étale pushforward

Compatibility entry for the canonical construction of an `f`-map from a morphism into
small étale pushforward.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FMap.ofPushforwardHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1))}
    {ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))},
    (𝒢 ⟶ (sheafPushforwardType f).obj ℱ) → FMap f 𝒢 ℱ)
