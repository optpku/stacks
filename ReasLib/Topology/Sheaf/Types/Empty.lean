/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Empty sections of type-valued sheaves

This module provides the canonical singleton-section instance for a type-valued sheaf evaluated
on the empty open set.
-/

@[expose] public section

open CategoryTheory.Limits Opposite TopCat

noncomputable section

universe u v

namespace TopCat.Sheaf.Type

variable {X : TopCat.{u}}

/-- Sections of a type-valued sheaf over the empty open form a singleton type. -/
noncomputable instance emptySectionsUnique (F : X.Sheaf (Type v)) :
    Unique (F.obj.obj (op ⊥)) :=
  Types.isTerminalEquivUnique _ F.isTerminalOfEmpty

end TopCat.Sheaf.Type

end

end
