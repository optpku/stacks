/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Sequential

/-!
# Standard colimit presentations of sequential filtrations

`SequentialColimitFiltration` is the source-facing, stage-and-step presentation of a sequential
colimit.  This leaf exposes the same data through Mathlib's neutral `ColimitPresentation` owner,
so constructions written for arbitrary colimit presentations can consume a sequential filtration
without rebuilding its diagram or cocone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.SequentialColimitFiltration

variable {C : Type u} [Category.{v} C]

/-- The canonical Mathlib colimit presentation carried by a sequential filtration. -/
abbrev toColimitPresentation {P : C} (F : SequentialColimitFiltration P) :
    ColimitPresentation ℕ P where
  diag := F.diagram
  ι := F.toCocone
  isColimit := F.isColimit

/-- The standard presentation has the filtration's stage diagram. -/
@[simp]
theorem toColimitPresentation_diag {P : C} (F : SequentialColimitFiltration P) :
    F.toColimitPresentation.diag = F.diagram := rfl

/-- The standard presentation has the filtration's cocone legs. -/
@[simp]
theorem toColimitPresentation_ι {P : C} (F : SequentialColimitFiltration P) :
    F.toColimitPresentation.ι = F.toCocone := rfl

/-- Every arrow in the sequential index category satisfies the filtration cocone equation. -/
@[reassoc]
theorem map_comp_toCoconeApp {P : C} (F : SequentialColimitFiltration P)
    {i j : ℕ} (f : i ⟶ j) :
    F.diagram.map f ≫ F.coconeApp j = F.coconeApp i := by
  exact F.toColimitPresentation.w f

/-- The standard presentation exposes the same chosen colimit instance as the filtration. -/
theorem toColimitPresentation_hasColimit {P : C} (F : SequentialColimitFiltration P) :
    F.toColimitPresentation.hasColimit = F.instHasColimit := rfl

end CategoryTheory.SequentialColimitFiltration
