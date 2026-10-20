module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Retracts
import StacksCheckRecall

/-!
# Lemma 15.82.8 (0676)

@stack 0676
-/

@[expose] public section

/- Lemma 15.82.8 (1): both summands of a relatively `m`-pseudo-coherent biproduct are relatively
`m`-pseudo-coherent. -/
@[stacks 0676 "(1), m-pseudo-coherent summands"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo.summands_of_biprod

/- Lemma 15.82.8 (2): both summands of a relatively pseudo-coherent biproduct are relatively
pseudo-coherent. -/
@[stacks 0676 "(2), pseudo-coherent summands"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo.summands_of_biprod
