/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Short Exact Complexes as an Object Property

This file supplies the neutral object-property owner used when a construction
is functorial in short exact complexes rather than merely defined pointwise.
-/

universe v u

namespace CategoryTheory.ShortComplex

variable (A : Type u) [Category.{v} A] [Preadditive A]

/-- Short exact complexes, regarded as an object property on `ShortComplex A`. -/
@[stacks 010L "short exact complexes as an object property"]
def shortExact : ObjectProperty (ShortComplex A) :=
  fun S ↦ S.ShortExact

/-- Membership in `shortExact A` is the usual short-exactness predicate. -/
@[simp]
theorem mem_shortExact (S : ShortComplex A) :
    shortExact A S ↔ S.ShortExact := sorry

end CategoryTheory.ShortComplex
