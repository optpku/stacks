module

public import stacks_project.Chap10.Lemma_10_75_3
import StacksCheckRecall

/-!
# Remark 10.75.4

@stack 00M2

The source fixes the comparison isomorphism from Lemma 10.75.3 while postponing sign conventions.
This editorial remark therefore directly recalls that concrete comparison.
-/

@[expose] public section

/- Remark 10.75.4: the homology comparison isomorphism constructed in Lemma `10.75.3` is the
chosen comparison to use in the chapter, even though the sign conventions in homological algebra
mean that this is only the “correct” comparison up to signs. -/
@[stacks 00M2]
#check @resolved_double_complex_homology_comparison
