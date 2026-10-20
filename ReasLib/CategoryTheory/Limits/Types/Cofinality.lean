/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal
open scoped Cardinal

namespace CategoryTheory.Limits.Types

/-- A map from a set of cardinality below the cofinality of an ordinal into a colimit of
sets indexed by that ordinal's predecessors factors through a single stage. -/
theorem exists_lift_of_lt_cof {β : Ordinal.{u}} {F : β.ToType ⥤ Type u} {c : Cocone F}
    (hc : IsColimit c) {S : Type u} (φ : S ⟶ c.pt) (hS : #S < β.cof) :
    ∃ (α : β.ToType) (φα : S ⟶ F.obj α), φα ≫ c.ι.app α = φ := sorry

end CategoryTheory.Limits.Types
