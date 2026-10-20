/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations.StrongTrans

/-!
# Strong transformations for setoid-fibred absolute inertia

Aggregate import for stable-universe forget/section/equivalence data and their strong
transformation packaging. New users can import `Maps` for concrete maps, `Naturality` for direct
and packaged laws, or `StrongTrans` for the coherent `forget.strongTrans`, `forget.pointwiseEquivalence`, and
`forget.pseudofunctorEquivalence` owners.
-/

@[expose] public section
