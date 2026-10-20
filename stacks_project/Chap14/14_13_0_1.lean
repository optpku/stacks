/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower
public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily
import StacksCheckRecall

/-!
@stack 017B
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w}) (V W : SimplicialObject C)
variable (F : Functor.indexedCoprod.HomFamily U V W)

/- Equation 14.13.0.1: simplex-indexed degreewise morphisms define a copower morphism exactly
when they commute with every simplicial operator. -/
@[stacks 017B "Equation 14.13.0.1"]
#check (Functor.indexedCoprod.HomFamily.isCompatible_iff F :
  Functor.indexedCoprod.HomFamily.IsCompatible F ↔
    ∀ ⦃Δ Δ' : SimplexCategoryᵒᵖ⦄ (f : Δ ⟶ Δ') (u : U.obj Δ),
      V.map f ≫ F Δ' (U.map f u) = F Δ u ≫ W.map f)

end CategoryTheory
