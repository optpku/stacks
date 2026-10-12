/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Projections.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for setoid-stack two-fibre-product projections

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

namespace StackOver.Setoids.TwoFibreProduct

/-- The first-projection component is the canonical direct first projection. -/
@[simp, stacks 0434 "setoid-stack first projection component computation"]
theorem pseudofunctor.fst.app (S : Bicategory.Cospan
    (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.fst J).app S =
      _root_.CategoryTheory.StackOver.Setoids.TwoFibreProduct.fst
        S.fst S.snd := sorry

/-- Forgetting the first-projection component recovers its ambient component. -/
@[simp, stacks 0434 "setoid-stack first projection ambient readout"]
theorem pseudofunctor.fst.app.toAmbient (S : Bicategory.Cospan
    (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.fst J).app S).hom =
      (pseudofunctor.fst.ambient J).app S := sorry

/-- The second-projection component is the canonical direct second projection. -/
@[simp, stacks 0434 "setoid-stack second projection component computation"]
theorem pseudofunctor.snd.app (S : Bicategory.Cospan
    (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.snd J).app S =
      _root_.CategoryTheory.StackOver.Setoids.TwoFibreProduct.snd
        S.fst S.snd := sorry

/-- Forgetting the second-projection component recovers its ambient component. -/
@[simp, stacks 0434 "setoid-stack second projection ambient readout"]
theorem pseudofunctor.snd.app.toAmbient (S : Bicategory.Cospan
    (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.snd J).app S).hom =
      (pseudofunctor.snd.ambient J).app S := sorry

end StackOver.Setoids.TwoFibreProduct

end CategoryTheory
