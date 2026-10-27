/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra

/-! Naturality of evaluation of free commutative algebra sheaves. -/

@[expose] public section

open CategoryTheory

universe c v w

namespace CategoryTheory.Sheaf.FreeAlgebra

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J CommRingCat.{w}]

/-- Postcomposing free-algebra evaluation with an algebra morphism is evaluation at the
postcomposed generator assignment. -/
theorem evaluation_naturality
    {A : Sheaf J CommRingCat.{w}} (B D : Under A) (g : B ⟶ D)
    (E : Sheaf J (Type w)) (α : E ⟶ (sheafForget J).obj B.right) :
    (evaluation B E α).right ≫ g.right =
      (evaluation D E (α ≫ (sheafForget J).map g.right)).right := sorry

end CategoryTheory.Sheaf.FreeAlgebra
