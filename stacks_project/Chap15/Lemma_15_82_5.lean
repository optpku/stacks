/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase
import StacksCheckRecall

/-!
# Lemma 15.82.5 (0673)

@stack 0673
-/

@[expose] public section

/- Lemma 15.82.5 (1): finite scalar restriction preserves and reflects relative
`m`-pseudo-coherence. -/
@[stacks 0673 "(1), finite scalar restriction"]
#check @CategoryTheory.DerivedCategory.isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite

/- Lemma 15.82.5 (2): finite scalar restriction preserves and reflects relative
pseudo-coherence. -/
@[stacks 0673 "(2), finite scalar restriction"]
#check @CategoryTheory.DerivedCategory.isPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
