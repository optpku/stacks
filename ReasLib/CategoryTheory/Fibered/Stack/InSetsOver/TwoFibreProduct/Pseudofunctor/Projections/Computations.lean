/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Pseudofunctor.Projections.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for set-stack two-fibre-product projections

This leaf identifies each lifted projection component with the direct projection datum and
exposes its ambient setoid-stack morphism.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

/-- The first-projection component is the direct first projection. -/
@[simp, stacks 0434 "set-stack first projection component"]
theorem pseudofunctor.fst.app (S : Bicategory.Cospan
    (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.fst J).app S =
      _root_.CategoryTheory.StackOver.Sets.TwoFibreProduct.fst
        S.fst S.snd := sorry

/-- Forgetting the first-projection component recovers its ambient component. -/
@[simp, stacks 0434 "set-stack first projection ambient readout"]
theorem pseudofunctor.fst.app.toAmbient (S : Bicategory.Cospan
    (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.fst J).app S).hom =
      (pseudofunctor.fst.ambient J).app S := sorry

/-- The second-projection component is the direct second projection. -/
@[simp, stacks 0434 "set-stack second projection component"]
theorem pseudofunctor.snd.app (S : Bicategory.Cospan
    (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.snd J).app S =
      _root_.CategoryTheory.StackOver.Sets.TwoFibreProduct.snd
        S.fst S.snd := sorry

/-- Forgetting the second-projection component recovers its ambient component. -/
@[simp, stacks 0434 "set-stack second projection ambient readout"]
theorem pseudofunctor.snd.app.toAmbient (S : Bicategory.Cospan
    (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.snd J).app S).hom =
      (pseudofunctor.snd.ambient J).app S := sorry

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
