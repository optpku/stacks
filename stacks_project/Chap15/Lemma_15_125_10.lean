module

public import ReasLib.LinearAlgebra.Matrix.UnimodularRow
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.125.10

@stack 0ASW

The source row condition is represented by `Matrix.IsUnimodularRow`; completion
to a general-linear matrix and the linear-combination criterion are reusable
API in the same leaf.
-/

/- Lemma 15.125.10: a finite unimodular row over a Bézout domain completes to an invertible
matrix with the given first row. -/
@[stacks 0ASW "Lemma 15.125.10, completion of a unimodular row"]
#check @Matrix.IsUnimodularRow.exists_generalLinearGroup

#check @Matrix.IsUnimodularRow.iff_surjective_linearCombination
#check @Matrix.IsUnimodularRow.exists_generalLinearGroup_of_surjective
#check @Matrix.IsUnimodularRow.of_generalLinearGroup
