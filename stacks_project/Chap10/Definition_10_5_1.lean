module

public import ReasLib.Algebra.Module.FinitePresentation.Exact
import StacksCheckRecall

/-!
# Definition 10.5.1

@stack 0518
-/

@[expose] public section

/- Definition 10.5.1 (1): finite modules are `Module.Finite`; the reusable finite-free
presentation criterion is owned by `Module.Finite.iff_exists_surjective_free`. -/
@[stacks 0518 "finite module"]
#check @Module.Finite
@[stacks 0518 "finite free presentation"]
#check @Module.Finite.iff_exists_surjective_free

/- Definition 10.5.1 (2): finitely presented modules are `Module.FinitePresentation`; the
reusable exact finite-free presentation criterion is owned by
`Module.FinitePresentation.iff_exists_exact_free_sequence`. -/
@[stacks 0518 "finite-presentation module"]
#check @Module.FinitePresentation
@[stacks 0518 "exact finite free presentation"]
#check @Module.FinitePresentation.iff_exists_exact_free_sequence
