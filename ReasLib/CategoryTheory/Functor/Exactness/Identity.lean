/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Exactness.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity exact functors

This file gives the identity functor its canonical bundled exact-functor
owner and records the basic underlying-functor computations.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.ExactFunctor

variable (C : Type u) [Category.{v} C]

/-- The identity functor, bundled as an exact functor. -/
@[stacks 015F "identity exact functor"]
noncomputable abbrev id : C ⥤ₑ C :=
  ExactFunctor.of (𝟭 C)

/-- The bundled exact identity carries the canonical additive structure of
the identity functor. -/
noncomputable instance id_additive [Preadditive C] : (id C).obj.Additive :=
  inferInstanceAs (𝟭 C).Additive

/-- The underlying functor of the bundled exact identity is the identity
functor. -/
@[simp]
theorem id_obj : (id C).obj = 𝟭 C := sorry

/-- The bundled exact identity fixes objects. -/
@[simp]
theorem id_obj_obj (X : C) : (id C).obj.obj X = X := sorry

/-- The bundled exact identity fixes morphisms. -/
@[simp]
theorem id_obj_map {X Y : C} (f : X ⟶ Y) :
    (id C).obj.map f = f := sorry

end CategoryTheory.ExactFunctor
