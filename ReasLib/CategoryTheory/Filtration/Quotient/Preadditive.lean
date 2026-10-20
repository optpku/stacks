/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Quotient.Map
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of filtration quotients

This is the category-independent additive owner for quotient-by-a-stage.  Complex-level quotient
functors inherit the instance through `Functor.mapHomologicalComplex`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]

/-- Quotienting a filtered object by a fixed stage is an additive functor. -/
@[stacks 0121 "additivity of the filtration quotient functor"]
noncomputable instance quotientFunctor_additive (p : ℤ) :
    (quotientFunctor (C := C) p).Additive := sorry

#synth (quotientFunctor (C := C) 0).Additive

end CategoryTheory.FilteredObject
