/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Subquotient.Map
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of filtered homological-complex subquotients

The fixed subquotient construction is additive in the filtered homological complex.  This is a
separate support owner so complex specializations can inherit it without local instances.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.HomologicalComplex.Filtered.Subquotient

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- A fixed filtration subquotient is an additive functor. -/
@[stacks 0BKI "additivity of the filtered subquotient functor"]
noncomputable instance functor_additive {p q : ℤ} (hpq : p ≤ q) :
    (functor (C := C) (c := c) hpq).Additive := sorry

end CategoryTheory.HomologicalComplex.Filtered.Subquotient
