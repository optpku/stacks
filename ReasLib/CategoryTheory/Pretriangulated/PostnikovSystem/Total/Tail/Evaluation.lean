/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Evaluation
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Tail.Basic

/-!
# Evaluation after Truncating Total Finite Postnikov Systems

This leaf records how row and auxiliary evaluation, and the canonical
auxiliary-to-row comparison, behave under the total tail functor.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Truncation followed by row evaluation at `i` is row evaluation at the successor position. -/
@[stacks 0D7Z "row evaluation after Postnikov truncation"]
theorem tail_comp_row (n : ℕ) (i : Fin (n + 1)) :
    tail D n ⋙ row D n i = row D (n + 1) i.succ := sorry

variable (D) in
/-- Truncation followed by auxiliary evaluation at `i` is auxiliary evaluation at the
successor position. -/
@[stacks 0D7Z "auxiliary evaluation after Postnikov truncation"]
theorem tail_comp_aux (n : ℕ) (i : Fin (n + 1)) :
    tail D n ⋙ aux D n i = aux D (n + 1) i.succ := sorry

/-- The auxiliary-to-row comparison of a tail is the successor component of the original
auxiliary-to-row comparison. -/
@[simp, stacks 0D7Z "auxiliary-to-row comparison after Postnikov truncation"]
theorem tail_toRow_app {n : ℕ} (i : Fin (n + 1)) (P : Total D (n + 1)) :
    (toRow D n i).app ((tail D n).obj P) =
      (toRow D (n + 1) i.succ).app P := sorry

end CategoryTheory.PostnikovSystem.Total
