module

public import ReasLib.RingTheory.Completion.Krasner
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.114.1 (Krasner's lemma) (09EI)

@stack 09EI
-/

/- Lemma 15.114.1 (Krasner's lemma), Stacks `09EI` (current Stacks Lemma 15.115.1): simple roots
over a one-dimensional complete local domain persist under sufficiently small coefficient
perturbations. -/
@[stacks 09EI "Lemma 15.114.1, Krasner's lemma"]
#check @IsCompleteLocalRing.existsRoot_of_smallPerturbation
