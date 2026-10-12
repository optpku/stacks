/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.LocalizationAwaySplit
import StacksCheckRecall

/-!
# Lemma 15.77.2 (0A1U)

@stack 0A1U

The principal-localization splitting theorem is owned by the pseudo-coherent derived-category
leaf.  This Chapter file records the official source label and its canonical comparison map.
-/

@[expose] public section

/- Lemma 15.77.2 (0A1U): a surjective residue-field homology comparison yields a principal-local
perfect upper truncation and a unique compatible splitting. -/
@[stacks 0A1U "Lemma 15.77.2, residue-field homology splitting"]
#check @CategoryTheory.exists_localizationAway_split_of_residueField_homology_surjective

@[stacks 0A1U "canonical derived scalar-extension homology comparison"]
#check @CategoryTheory.ModuleCat.derivedExtensionHomologyComparison

#print axioms CategoryTheory.exists_localizationAway_split_of_residueField_homology_surjective
