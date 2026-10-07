module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

@[expose] public section

open CategoryTheory Limits

/- Lemma 26.23.5: a base change of a monomorphism is a monomorphism. -/
@[stacks 02YC] #check pullback.snd_of_mono
