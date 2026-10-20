/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Sections

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X]

/-- Restriction of sections of a quasicoherent module on a locally Noetherian scheme to an open
containing all of its associated points is injective. -/
theorem injective_restrictionToOpen_of_associatedPoints_subset
    (U : X.Opens) (hU : associatedPoints ℱ ⊆ (U : Set X)) :
    Function.Injective (ℱ.val.map (TopologicalSpace.Opens.leTop U).op) := sorry

end AlgebraicGeometry.Scheme.Modules
