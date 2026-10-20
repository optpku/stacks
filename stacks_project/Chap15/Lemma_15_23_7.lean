module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.7

@stack 0EB9

Flat base change of a finite reflexive module is a reusable owner-level theorem.
-/

@[expose] public section

/- Lemma 15.23.7: flat base change between Noetherian domains preserves reflexivity. -/
@[stacks 0EB9 "Lemma 15.23.7"]
#check @Module.IsReflexive.baseChange_of_flat
