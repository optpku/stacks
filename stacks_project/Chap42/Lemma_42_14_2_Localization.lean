/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.Localization

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Opens

variable {X : Scheme.{u}}

/-- The defining ideal of the canonical reduced closed complement of an open subscheme. -/
noncomputable abbrev reducedComplement (U : X.Opens) : X.IdealSheafData :=
  (ClosedSubschemeStructure.reduced U.compl).ideal

end AlgebraicGeometry.Scheme.Opens
