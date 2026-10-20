module

public import Mathlib.Algebra.Module.FinitePresentation
import StacksCheckRecall

/-!
# Finiteness over Noetherian rings

@stack 00IK

Lemma 10.51.1 records finite presentation, finite submodules, and the
ascending chain condition over Noetherian rings.
-/

@[expose] public section

@[stacks 00IK "(1), finite presentation"]
#check @Module.finitePresentation_of_finite

@[stacks 00IK "(2), finite submodules"]
#check @isNoetherian_of_submodule_of_noetherian

@[stacks 00IK "(3), ascending chain condition"]
#check @monotone_stabilizes_iff_noetherian
