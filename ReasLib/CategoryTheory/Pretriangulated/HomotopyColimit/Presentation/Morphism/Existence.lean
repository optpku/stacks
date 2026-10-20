/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of Morphisms of Telescope Presentations

Existence statements for presentation morphisms and their stage-compatible maps on the
presented homotopy-colimit objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 0CRI, Remark 13.33.3: every morphism of sequential diagrams admits a compatible
morphism between any two explicit telescope presentations. -/
@[stacks 0CRI "functoriality of homotopy-colimit presentations"]
theorem Presentation.nonemptyHom {S T : ℕ ⥤ D} (α : S ⟶ T)
    {X Y : D} (P : Presentation S X) (Q : Presentation T Y) :
    Nonempty (Presentation.Hom α P Q) := sorry

/-- Every morphism of sequential diagrams induces some map between the presented
homotopy-colimit objects that is compatible with every canonical stage map. -/
@[stacks 0CRI "stage-compatible map between homotopy colimits"]
theorem Presentation.existsStageMap {S T : ℕ ⥤ D} (α : S ⟶ T)
    {X Y : D} (P : Presentation S X) (Q : Presentation T Y) :
    ∃ h : X ⟶ Y, ∀ n : ℕ, P.ι n ≫ h = α.app n ≫ Q.ι n := sorry

end CategoryTheory.HomotopyColimit
