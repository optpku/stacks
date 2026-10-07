module

public import ReasLib.RingTheory.CompleteIntersection.OverField.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.135.7

@stack 00SF

The five local presentation criteria are owned by the field-relative complete-intersection
comparison API.
-/

@[stacks 00SF "local complete-intersection presentation criteria over a field"]
#check @Algebra.IsCompleteIntersectionOver.local_tfae

/- Canonical predicates appearing in the five source clauses. -/
#check @Algebra.IsCompleteIntersectionOver
#check @RingHom.KernelIsGeneratedByRegularSequence
#check @IsGlobalCompleteIntersection
#check @IsLocalCompleteIntersection
