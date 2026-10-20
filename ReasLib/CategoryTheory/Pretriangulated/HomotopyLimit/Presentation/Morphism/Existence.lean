/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of Morphisms of Homotopy-Limit Presentations

Existence statements for presentation morphisms and their stage-compatible maps on the
presented homotopy-limit objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 08TC: every morphism of sequential inverse systems admits a compatible morphism
between any two explicit homotopy-limit presentations. -/
@[stacks 08TC "functoriality of homotopy-limit presentations"]
theorem Presentation.nonemptyHom {K L : SequentialInverseSystem D} (α : K ⟶ L)
    {X Y : D} (P : Presentation K X) (Q : Presentation L Y) :
    Nonempty (Presentation.Hom α P Q) := sorry

/-- Every morphism of sequential inverse systems induces some map between the presented
homotopy-limit objects that is compatible with every canonical stage projection. -/
@[stacks 08TC "stage-compatible map between homotopy limits"]
theorem Presentation.existsStageMap {K L : SequentialInverseSystem D} (α : K ⟶ L)
    {X Y : D} (P : Presentation K X) (Q : Presentation L Y) :
    ∃ h : X ⟶ Y, ∀ n : ℕ,
      P.stageProjection n ≫ α.app (op n) = h ≫ Q.stageProjection n := sorry

end CategoryTheory.HomotopyLimit
