module

public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.Separable
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.43.9

Lemma 10.43.9 (Tag 0C2Y) is a canonical recall of invariance of geometric
reducedness under a separable algebraic change of the ground field.  The
theorem is owned by `Algebra.IsGeometricallyReduced` so it can be imported
without depending on Chapter 10.

@stack 0C2Y
-/

@[stacks 0C2Y]
#check @Algebra.IsGeometricallyReduced.iff_of_isSeparable
