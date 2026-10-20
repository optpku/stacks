/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ResidueField
import StacksCheckRecall

/-!
# Lemma 15.78.3 (068W)

@stack 068W

The prime-local and maximal-local recognition criteria are owned by the derived-category
perfectness leaf. This Chapter file is their direct official-label recall.
-/

@[expose] public section

/- Lemma 15.78.3 (1) (068W): local perfectness is equivalent to eventual residue-field
homology vanishing. -/
@[stacks 068W "Lemma 15.78.3 (1)"]
#check @CategoryTheory.prime_and_maximal_localizations_and_residueField_vanishing_tfae_of_isPseudoCoherent

/- Lemma 15.78.3 (2) (068W): bounded-below pseudo-coherent objects also satisfy the global
perfectness criterion. -/
@[stacks 068W "Lemma 15.78.3 (2)"]
#check @CategoryTheory.perfect_primeLocalizations_maximalLocalizations_residueField_vanishing_tfae_of_isPseudoCoherent_of_isGE

#print axioms CategoryTheory.prime_and_maximal_localizations_and_residueField_vanishing_tfae_of_isPseudoCoherent
