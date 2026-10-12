/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.IntermediateField.Adjoin.Cardinality
public import Mathlib.Analysis.Complex.Cardinality
import StacksCheckRecall

@[expose] public section

/- Exercise 9.6.7: no countable subset of `ℂ` generates `ℂ` as a field extension of `ℚ`.
This is the concrete specialization of the cardinality theorem for an adjoined intermediate
field over a countable base. -/
@[stacks 09G0]
#check (IntermediateField.adjoin_ne_top_of_countable (F := ℚ) (E := ℂ)
  not_countable_complex :
  ∀ {s : Set ℂ}, s.Countable → IntermediateField.adjoin ℚ s ≠ ⊤)
