/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.FunctorCategory
public import ReasLib.AlgebraicTopology.CosimplicialObject.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018Z

# Abelian cosimplicial objects

`CosimplicialObject` is an opaque definition in mathlib, so functor-category instances do not
automatically unfold through it. This file registers the canonical abelian structure explicitly.
-/

@[expose] public section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- 018Z (Lemma 14.22.1 (1)): cosimplicial objects valued in an abelian category form an
abelian category. -/
@[stacks 018Z]
noncomputable instance abelian : Abelian (CosimplicialObject A) :=
  Abelian.functorCategoryAbelian

/-- Exactness of a short complex of cosimplicial objects is detected at every simplex. -/
@[stacks 018Z "pointwise exactness of cosimplicial objects"]
theorem exact_iff_forall_app (S : ShortComplex (CosimplicialObject A)) :
    S.Exact ↔ ∀ Delta : SimplexCategory,
      (S.map (evaluation A Delta)).Exact := sorry

end CategoryTheory.CosimplicialObject
