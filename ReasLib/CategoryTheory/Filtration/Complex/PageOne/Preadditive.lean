/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.PageOne
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of the boundary-model first page

The explicit first-page construction is a functor on filtered complexes.  Its additive structure
is kept separate from the boundary-map and association-comparison definitions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Page.One

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The boundary-model first-page functor is additive in filtered-complex morphisms. -/
@[stacks 012N "additivity of the boundary-model first-page functor"]
noncomputable instance functor_additive :
    (functor (C := C)).Additive := sorry

#synth (functor (C := C)).Additive

end CategoryTheory.FilteredComplex.Page.One
