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

/- 7.47.1.1: a sieve `S` on `U` is a collection of subsets `S(T) ⊂ Mor_C(T, U)` whose only extra
rule is closure under precomposition: if `(α : T ⟶ U) ∈ S(T)` and `g : T' ⟶ T`, then
`(α ∘ g : T' ⟶ U) ∈ S(T')`. This is the mathlib field `Sieve.downward_closed`, with diagrammatic
composition `g ≫ α` in place of `α ∘ g`. -/
@[stacks 00YY] #check (CategoryTheory.Sieve.precomp_mem :
  ∀ {C : Type u} [Category.{v} C] {U : C} (sieve : Sieve U) {T T' : C}
    (arrow : T ⟶ U) (_ : sieve arrow) (g : T' ⟶ T), sieve (g ≫ arrow))
