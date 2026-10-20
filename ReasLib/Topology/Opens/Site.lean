/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Spaces

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalSpace.Opens

/-- The underlying set of a pullback of open subsets over a common target is the intersection
of the underlying sets of the two source opens. -/
theorem pullback_coe_eq_intersection {T : Type*} [TopologicalSpace T] {U V W : Opens T}
    (f : U ⟶ W) (g : V ⟶ W) :
    (pullback f g : Set T) = (U : Set T) ∩ (V : Set T) := sorry

end TopologicalSpace.Opens
