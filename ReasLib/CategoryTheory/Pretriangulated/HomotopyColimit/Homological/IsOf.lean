/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological.Exactness
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Intrinsic Homotopy-Colimit Image Statements

These existence statements consume the intrinsic `HomotopyColimit.IsOf`
predicate without making a public choice of telescope presentation.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory.HomotopyColimit.IsOf

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A]
variable {K : ℕ ⥤ D} {X : D}

/-- An intrinsic homotopy-colimit witness admits a presentation whose image cocone is
colimiting when the functor preserves the coproducts of the terms and their shifts by one.
The existential retains the presentation needed for comparison computations. -/
@[stacks 0CRK]
theorem existsImageCocone (hK : HomotopyColimit.IsOf K X) (H : D ⥤ A)
    [HasColimitsOfShape ℕ A] [IsTriangulated D] [Abelian A]
    [Functor.IsHomological H] [HasExactColimitsOfShape ℕ A]
    [PreservesColimit (Discrete.functor K.obj) H]
    [PreservesColimit (Discrete.functor (fun n : ℕ ↦ (K.obj n)⟦(1 : ℤ)⟧)) H] :
    ∃ P : HomotopyColimit.Presentation K X,
      Nonempty (IsColimit (HomotopyColimit.Presentation.imageCocone P H)) := sorry

/-- Stacks 0CRK, Lemma 13.33.8: a homological functor preserving the coproducts of the terms of
`K` and their shifts by one sends an intrinsic sequential homotopy colimit of `K` to a colimit
of the image sequence. -/
@[stacks 0CRK]
theorem existsImageIsColimit (hK : HomotopyColimit.IsOf K X) (H : D ⥤ A)
    [HasColimitsOfShape ℕ A] [IsTriangulated D] [Abelian A]
    [Functor.IsHomological H] [HasExactColimitsOfShape ℕ A]
    [PreservesColimit (Discrete.functor K.obj) H]
    [PreservesColimit (Discrete.functor (fun n : ℕ ↦ (K.obj n)⟦(1 : ℤ)⟧)) H] :
    ∃ c : Cocone (K ⋙ H), ∃ hc : IsColimit c, c.pt = H.obj X := sorry

end CategoryTheory.HomotopyColimit.IsOf

end
