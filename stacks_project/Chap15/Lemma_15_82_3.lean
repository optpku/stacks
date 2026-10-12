/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Presentation
import StacksCheckRecall

/-!
# Lemma 15.82.3 (065H)

@stack 065H

Relative pseudo-coherence may be checked on one surjective polynomial presentation or on every
such presentation.
-/

@[expose] public section

/- Lemma 15.82.3 (1), tag `065H`: the owner predicate uses every surjective polynomial
presentation, while this theorem gives the equivalent existence of one presentation. -/
@[stacks 065H "(1), relative m-pseudo-coherence over some or every presentation"]
#check @CategoryTheory.CochainComplex.isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation

/- Lemma 15.82.3 (2), tag `065H`: relative pseudo-coherence can likewise be checked on every
surjective polynomial presentation. -/
@[stacks 065H "(2), relative pseudo-coherence over every presentation"]
#check @CategoryTheory.CochainComplex.isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation

/- Lemma 15.82.3 (2), companion existence form. -/
@[stacks 065H "(2), relative pseudo-coherence over some presentation"]
#check @CategoryTheory.CochainComplex.isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
