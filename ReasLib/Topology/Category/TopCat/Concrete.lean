/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Concrete-category facts about `TopCat`

This module owns categorical properties of the standard forgetful functor from topological spaces
to types that are not supplied by Mathlib's basic `TopCat` API.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- The forgetful functor `TopCat ⥤ Type` does not reflect isomorphisms. -/
theorem forget_not_reflectsIsomorphisms :
    ¬ (forget TopCat.{u}).ReflectsIsomorphisms := sorry

end TopCat
