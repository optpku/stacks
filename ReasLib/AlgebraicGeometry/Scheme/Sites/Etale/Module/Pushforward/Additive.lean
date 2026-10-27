/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Continuous small-étale pushforward of module sheaves is additive. -/
instance etaleModulePushforward_additive
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [Ring Λ] :
    (etaleModulePushforward f Λ).Additive := sorry

end AlgebraicGeometry.Scheme.Etale
