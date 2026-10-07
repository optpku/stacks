module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.KoszulLimit.Nonpositive
import StacksCheckRecall

/-!
# Lemma 15.92.19: positive cohomology and the first powered Koszul stage

The reusable owner contains the source-facing three-way criterion for a derived-complete object,
its derived reduction, and the first powered Koszul stage.

@stack 0H83
-/

@[expose] public section

/- Lemma 15.92.19 (0H83): for a derived-complete object `K`, vanishing of positive cohomology is
equivalent for `K`, for `K ⊗ᴸ_A (A/I)[0]`, and for `K` tensored with the first powered Koszul
stage. -/
@[stacks 0H83 "Lemma 15.92.19"]
#check @CategoryTheory.DerivedCategory.KoszulLimit.isLE_zero_tfae_of_isDerivedComplete
