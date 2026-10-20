/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Sieve
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- 7.49.3.1: the sieve S'' on U is defined by the membership rule that
f : T ⟶ U lies in S''(T) iff there exist V, α : V ⟶ U in S(V), and
g : T ⟶ V in the refinement sieve S_{V,α}(T) with f = α ∘ g. This is the
sieve Sieve.bind S R obtained by binding S with the sieve-valued family
R α = S_{V,α}. Source composition f = α ∘ g is BindStruct.fac : g ≫ α = f. -/
@[stacks 00ZK] #check (CategoryTheory.Sieve.mem_bind_iff :
  ∀ {C : Type u} [Category.{v} C] {U : C} (sieve : Sieve U)
    (refinements : ∀ ⦃V : C⦄ ⦃outerArrow : V ⟶ U⦄, sieve outerArrow → Sieve V)
    {T : C} (arrow : T ⟶ U),
    Sieve.bind sieve.arrows refinements arrow ↔
      ∃ (V : C) (outerArrow : V ⟶ U) (outer_mem : sieve outerArrow)
        (innerArrow : T ⟶ V),
        refinements outer_mem innerArrow ∧ arrow = innerArrow ≫ outerArrow)

#check CategoryTheory.Sieve.BindStruct
#check CategoryTheory.Presieve.BindStruct.bind
