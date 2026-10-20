/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory.Abelian
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Tag 013C: an object of an abelian category is projective exactly when its
preadditive co-Yoneda functor is exact. -/
@[stacks 013C]
theorem projective_iff_exact_preadditiveCoyonedaObj (P : C) :
    Projective P ↔ exactFunctor _ _ (preadditiveCoyonedaObj P) := sorry

/-- Tag 013C: an object is projective exactly when every short exact sequence ending at it has a
split second map. -/
@[stacks 013C]
theorem projective_iff_shortExact_isSplitEpi (P : C) :
    Projective P ↔
      ∀ ⦃S : ShortComplex C⦄, S.X₃ = P → S.ShortExact → IsSplitEpi S.g := sorry

end CategoryTheory
