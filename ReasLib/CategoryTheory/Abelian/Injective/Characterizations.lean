/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterizations of Injective Objects

@stack 0136
-/

@[expose] public section

open CategoryTheory.Abelian
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Tag 0136: an object of an abelian category is injective exactly when its
preadditive Yoneda functor is exact. -/
@[stacks 0136]
theorem injective_iff_exact_preadditiveYonedaObj (I : C) :
    Injective I ↔ exactFunctor _ _ (preadditiveYonedaObj I) := sorry

/-- Tag 0136: an object is injective exactly when every short exact sequence beginning at it has
a split first map. -/
@[stacks 0136]
theorem injective_iff_shortExact_isSplitMono (I : C) :
    Injective I ↔
      ∀ ⦃S : ShortComplex C⦄, S.X₁ = I → S.ShortExact → IsSplitMono S.f := sorry

end CategoryTheory
