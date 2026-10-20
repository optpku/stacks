/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

/-!
# Global sections on basic opens
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Restriction of the global sections of a quasi-coherent module to a basic open is
localization at the powers of the defining global function. -/
instance globalSections_isLocalizedModule_basicOpen
    [CompactSpace X] [QuasiSeparatedSpace X] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (f : Γ(X, ⊤)) :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)) := sorry

end AlgebraicGeometry.Scheme.Modules
