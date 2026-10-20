/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.BigQuasicoherent
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Colimits of quasicoherent modules on big standard sites

This module records the existence of colimits in the category of
quasicoherent module sheaves on a big standard site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent

/-- Quasicoherent modules on a big standard site have colimits of every
universe-compatible shape. -/
theorem hasColimitsOfShape (S : Scheme.{u}) (τ : StandardTopology)
    (J : Type v) [Category.{w} J] :
    HasColimitsOfShape J
      (SheafOfModules.isQuasicoherent
        (bigStructureSheaf τ S)).FullSubcategory := sorry

end AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent
