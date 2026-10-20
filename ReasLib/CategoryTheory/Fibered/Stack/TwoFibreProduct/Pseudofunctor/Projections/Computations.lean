/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Projections.Construction

/-!
# Component computations for stack-valued two-fibre-product projections

These lemmas identify the lifted projection components with the canonical direct projections and
expose their ambient morphisms.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.TwoFibreProduct

/-- The first-projection component is the canonical direct first projection. -/
@[simp, stacks 02ZL "first projection component of stack two-fibre products"]
theorem pseudofunctor.fst.app (S : Bicategory.Cospan
    (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.fst J).app S =
      _root_.CategoryTheory.StackOver.Groupoids.TwoFibreProduct.fst
        S.fst S.snd := sorry

/-- Forgetting the first-projection component recovers its ambient component. -/
@[simp, stacks 02ZL "ambient first projection component readout"]
theorem pseudofunctor.fst.app.toAmbient (S : Bicategory.Cospan
    (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.fst J).app S).hom =
      (pseudofunctor.fst.ambient J).app S := sorry

/-- The second-projection component is the canonical direct second projection. -/
@[simp, stacks 02ZL "second projection component of stack two-fibre products"]
theorem pseudofunctor.snd.app (S : Bicategory.Cospan
    (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.snd J).app S =
      _root_.CategoryTheory.StackOver.Groupoids.TwoFibreProduct.snd
        S.fst S.snd := sorry

/-- Forgetting the second-projection component recovers its ambient component. -/
@[simp, stacks 02ZL "ambient second projection component readout"]
theorem pseudofunctor.snd.app.toAmbient (S : Bicategory.Cospan
    (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.snd J).app S).hom =
      (pseudofunctor.snd.ambient J).app S := sorry

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
