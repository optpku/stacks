/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- Restriction of sections of a quasicoherent module to an open containing all of its weakly
associated points is injective. -/
theorem injective_restrictionToOpen_of_weakAss_subset
    (U : X.Opens) (hU : ℱ.weakAss ⊆ (U : Set X)) :
    Function.Injective (ℱ.val.map (TopologicalSpace.Opens.leTop U).op) := sorry

end AlgebraicGeometry.Scheme.Modules
