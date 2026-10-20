/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback.Module

@[expose] public section
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace AlgebraicGeometry.StandardTopology.Big

/-- The morphism of big standard sites induced by a scheme morphism is flat. -/
theorem pullbackRingedHom_isFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (τ : StandardTopology) :
    @RingedSite.Hom.IsFlat.{u} _ _ (pullbackRingedHom τ f)
      (pullbackRingedHom_modulePushforward_isRightAdjoint τ f) := sorry

end AlgebraicGeometry.StandardTopology.Big
