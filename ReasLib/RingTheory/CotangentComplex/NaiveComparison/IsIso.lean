/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison

/-!
# Isomorphism of the canonical naive cotangent comparison

For every commutative ring map, the canonical comparison from the naive
cotangent complex of the self-presentation to the truncation of the cotangent
complex is an isomorphism in the derived category.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace Algebra.NaiveCotangent

/-- The canonical self-presentation comparison is an isomorphism in the derived category. -/
instance toTruncGE_self_isIso (A : CommRingCat.{u}) (B : Under A) :
    IsIso (toTruncGE_self A B) := sorry

end Algebra.NaiveCotangent
