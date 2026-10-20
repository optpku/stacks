/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C]

/- Remark 48.32.4: the diagonal inverse system associated to explicit increasing sequential
representatives has the same Hom-colimit as the iterated system. -/
@[stacks 0G53] #check
  (CategoryTheory.Pro.SequentialHom.diagonalToIteratedHom_bijective :
    ∀ {M : ℕ → ℕᵒᵖ ⥤ C}
      (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
      (h_ge : ∀ k n, n ≤ (r k).reindex n) (N : C),
      Function.Bijective
        ((CategoryTheory.Pro.SequentialHom.diagonalToIteratedHom M r).app N))

end CategoryTheory.Pro.SequentialHom
