module

public import ReasLib.RingTheory.AdicCompletion.LocalMap.Flat
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.43.9 (0AGX)

@stack 0AGX
-/

/- Lemma 15.43.9, Stacks `0AGX`: a flat local map preserving the maximal ideal and residue field
induces an isomorphism on maximal-ideal completions. -/
@[stacks 0AGX "Lemma 15.43.9, flat local maps and completions"]
#check @AdicCompletion.mapLocal_bijective_of_flat
