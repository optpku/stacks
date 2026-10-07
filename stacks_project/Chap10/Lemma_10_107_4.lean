module

public import Mathlib.CategoryTheory.Category.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.107.4

@stack 04VR
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.107.4: if `A ⟶ B ⟶ C` are ring maps and the composite `A ⟶ C` is an epimorphism, then
`B ⟶ C` is an epimorphism. This is the general categorical fact that if `f ≫ g` is epic, then
`g` is epic. -/
@[stacks 04VR]
#check @CategoryTheory.epi_of_epi
