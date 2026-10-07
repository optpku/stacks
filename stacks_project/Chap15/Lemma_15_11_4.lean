module

public import Mathlib.RingTheory.Henselian
import StacksCheckRecall

/-!
# Adically complete henselian pairs

Mathlib already owns the exact bridge from `I`-adic completeness to the henselian-pair
structure, so this chapter item is a direct canonical recall.

@stack 0ALJ
-/

@[expose] public section

/- Lemma 15.11.4: if `A` is `I`-adically complete, then `(A, I)` is a henselian pair. -/
@[stacks 0ALJ "adic completeness implies henselianity"]
#check @IsAdicComplete.henselianRing
