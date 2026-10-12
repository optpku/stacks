/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# The based Yoneda equivalence

This file owns the choice-free property that identity-slice evaluation is an equivalence for a
category fibred in groupoids. Explicit inverse data obtained from a cleavage live in the focused
`Yoneda.Section` subtree.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace BasedCategory.Yoneda

/-- Stacks 004B: for a category fibred in groupoids, evaluation at the identity slice object is
an equivalence from based functors `C/U ⥤ S` to the fiber `S_U`. -/
@[stacks 004B]
noncomputable instance evaluation.isEquivalence
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] (U : C) :
    (evaluation p U).IsEquivalence := sorry

end BasedCategory.Yoneda

end CategoryTheory
