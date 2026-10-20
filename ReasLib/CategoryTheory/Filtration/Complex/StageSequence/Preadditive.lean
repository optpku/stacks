/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of selected filtration-stage sequences

An antitone sequence of filtration stages is additive in the filtered complex.  This support leaf
registers that fact independently of the sequential cocone and limit-stage constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.StageSequence

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A stage sequence selected by an antitone index function is additive. -/
@[stacks 0D8Z "additivity of an antitone filtration-stage sequence"]
noncomputable instance functor_additive (p : ℕ → ℤ) (hp : Antitone p) :
    (functor (C := C) p hp).Additive := sorry

#synth (functor (C := C) (fun n => (0 : ℤ)) (by
  intro a b hab
  rfl)).Additive

end CategoryTheory.FilteredComplex.StageSequence
