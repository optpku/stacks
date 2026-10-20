/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ReasLib.CategoryTheory.Functor.Objwise
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Objectwise properties of the simplex-category forgetful functor

The underlying ordered type of every simplex is finite and nonempty. This file exposes those
facts through the reusable objectwise functor interfaces.
-/

@[expose] public section

open CategoryTheory

namespace SimplexCategory.forget

/-- The forgetful functor from the simplex category is objectwise finite. -/
@[stacks 0165 "simplex objects are finite"]
instance objFinite : (CategoryTheory.forget SimplexCategory).ObjFinite :=
  ⟨fun _ ↦ inferInstance⟩

/-- The forgetful functor from the simplex category is objectwise nonempty. -/
@[stacks 0165 "simplex objects are nonempty"]
instance objNonempty : (CategoryTheory.forget SimplexCategory).ObjNonempty :=
  ⟨fun _ ↦ inferInstance⟩

end SimplexCategory.forget
