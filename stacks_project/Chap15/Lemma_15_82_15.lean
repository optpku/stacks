module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase
import StacksCheckRecall

/-!
# Lemma 15.82.15

@stack 067D
-/

@[expose] public section

/-!
# Lemma 15.82.15 compatibility entry point

The intermediate-base comparison API for relative pseudo-coherence is owned
by `ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase`.
-/

/- Lemma 15.82.15 (1), tag `067D`: intermediate-base comparison for relative
`m`-pseudo-coherence. -/
@[stacks 067D "(1), intermediate-base relative m-pseudo-coherence"]
#check @CategoryTheory.DerivedCategory.isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo

/- Lemma 15.82.15 (2), tag `067D`: intermediate-base comparison for relative
pseudo-coherence. -/
@[stacks 067D "(2), intermediate-base relative pseudo-coherence"]
#check @CategoryTheory.DerivedCategory.isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
