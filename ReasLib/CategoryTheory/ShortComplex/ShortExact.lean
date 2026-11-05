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

`CategoryTheory.ShortComplex.shortExact` is vendored verbatim from
`Mathlib.Algebra.Homology.ShortComplex.ShortExact` at commit
`d0207795ac79006da92d98544e1ce915ae386160`. When bumping mathlib to include
that declaration, remove this copy and use the upstream declaration; any
compatibility alias must point to it. Pending that bump, this in-place copy
needs a vendored-allowlist entry (COLLAB.md §11).
-/

universe v u

namespace CategoryTheory.ShortComplex

/-- `ShortComplex.ShortExact` as an object property. -/
abbrev shortExact (C : Type*) [Category* C] [Limits.HasZeroMorphisms C] :
    ObjectProperty (ShortComplex C) :=
  ShortComplex.ShortExact

variable (A : Type u) [Category.{v} A] [Limits.HasZeroMorphisms A]

/-- Membership in `shortExact A` is the usual short-exactness predicate. -/
@[simp]
theorem mem_shortExact (S : ShortComplex A) :
    shortExact A S ↔ S.ShortExact := Iff.rfl

end CategoryTheory.ShortComplex
