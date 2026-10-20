/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower
public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.Tensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of simplicial copowers

The Fubini maps and associativity isomorphism are owned at their natural generality by
`Functor.indexedCoprod.tensorIso`. This file records the remaining simplicial constant-factor
existence constructor and checks the generic isomorphism at the copower specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.HasConstCopowers

/-- To copower constant objects by `U ⊗ V`, it suffices that `V` copowers constant objects
and that `U` copowers arbitrary simplicial objects. This mixed Fubini owner is an explicit
constructor so fixed tensor copowers retain a unique automatic instance path. -/
@[stacks 017L "constant tensor-copower existence"]
abbrev tensor (U V : SSet.{uS}) (C : Type uC)
    [Category.{vC} C] [SimplicialObject.HasCopowers U C]
    [SimplicialObject.HasConstCopowers V C] :
    SimplicialObject.HasConstCopowers (U ⊗ V) C :=
  ⟨fun X ↦ Functor.HasIndexedCoprod.tensor U V ((SimplicialObject.const C).obj X)⟩

end CategoryTheory.SimplicialObject.HasConstCopowers

section

variable {C : Type uC} [Category.{vC} C]
variable (U V : SSet.{uS}) (X : SimplicialObject C)
variable [SimplicialObject.HasCopower V X]
variable [SimplicialObject.HasCopower U (SimplicialObject.copower V X)]

end
