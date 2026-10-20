module

public import Mathlib.RingTheory.Etale.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.143.8

@stack 00U7

The common-base etale comparison is already owned by Mathlib as
`Algebra.Etale.of_restrictScalars`.  This chapter file keeps only the
source-labelled recall.
-/

/- Lemma 10.143.8 (Tag 00U7): etale algebras over a common base are etale over one another. -/
@[stacks 00U7]
#check @Algebra.Etale.of_restrictScalars
