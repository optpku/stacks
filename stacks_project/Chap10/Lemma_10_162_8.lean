module

public import ReasLib.RingTheory.Completion.Nagata
import StacksCheckRecall

@[expose] public section

/-!
# Nagata Complete Local Rings

@stack 032W

This chapter item is a source-facing recall of the reusable complete-local
Nagata API.
-/

-- Lemma 10.162.8, tag `032W`: a Noetherian complete local ring is Nagata.
@[stacks 032W]
#check @IsCompleteLocalRing.nagataRing
