/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Triangulated.Coflat
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Triangulated

universe u v

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated] (X : D)

/- Lemma 57.6.1: the category of arrows `E ⟶ X` with `P E` is filtered. -/
@[stacks 0FYF] #check
  (CategoryTheory.ObjectProperty.representablyCoflat_ι P : RepresentablyCoflat P.ι)
