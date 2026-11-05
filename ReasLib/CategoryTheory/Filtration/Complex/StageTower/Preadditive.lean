/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.StageTower
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of the filtration-stage tower

The integer tower is a functor on filtered cochain complexes.  Its additive instance is kept in a
small support leaf so tower computations can import it without pulling in convergence APIs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.StageTower

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The integer filtration-stage tower is additive in a preadditive coefficient category. -/
@[stacks 012L "additivity of the integer filtration-stage tower"]
noncomputable instance functor_additive :
    (functor (C := C)).Additive := sorry

end CategoryTheory.FilteredComplex.StageTower
