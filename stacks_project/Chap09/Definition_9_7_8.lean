/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.7.8: a number field is the canonical mathlib class `NumberField`, i.e. a field of
characteristic `0` that is finite-dimensional over `ℚ`. -/
@[stacks 09GA]
#check NumberField

/- Companion recalls: the defining textbook properties of a number field are provided by the
canonical `NumberField` instances. -/
#check NumberField.to_charZero
#check NumberField.to_finiteDimensional
