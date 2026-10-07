module

public import ReasLib.Algebra.Module.FinitePresentation.PrincipalPure
import StacksCheckRecall

/-!
# Lemma 15.125.1 (0ASM)

@stack 0ASM

The principal-pure lifting criterion is owned by the ReasLib module leaf;
this Chapter file is a direct source-label recall.
-/

@[expose] public section

/- Lemma 15.125.1 (0ASM): cyclic-quotient direct summands are characterized by
surjectivity across principal-pure short exact sequences. -/
@[stacks 0ASM "Lemma 15.125.1, principal-pure lifting criterion"]
#check @directSummand_iff_surjective_compRight_of_principalPure_shortExact

#print axioms directSummand_iff_surjective_compRight_of_principalPure_shortExact
