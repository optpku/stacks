/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback

/-!
# Module pullback between standard big sites

This module records the adjunction used to form inverse images of module
sheaves along canonical pullback morphisms of standard big ringed sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Module pushforward along the canonical same-topology pullback morphism has
the canonical inverse-image left adjoint. -/
@[instance] theorem pullbackRingedHom_modulePushforward_isRightAdjoint
    (τ : StandardTopology) {S T : Scheme.{u}} (f : T ⟶ S) :
    ((pullbackRingedHom τ f).modulePushforward.{u}).IsRightAdjoint := sorry

end AlgebraicGeometry.StandardTopology.Big
