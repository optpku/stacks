module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Restriction
import StacksCheckRecall

/-!
# Lemma 15.82.2 (065G)

@stack 065G
-/

@[expose] public section

/- Lemma 15.82.2 (065G): a derived `R`-complex is `m`-pseudo-coherent exactly when its
restriction along the evaluation map `R[X] → R`, `X ↦ 0`, is `m`-pseudo-coherent. -/
@[stacks 065G "Lemma 15.82.2"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.iff_restrictScalars_polynomialEvalZero
