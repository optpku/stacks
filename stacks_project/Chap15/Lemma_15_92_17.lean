module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.KoszulLimit
import StacksCheckRecall

/-!
# Powered Koszul comparison with derived completion

The reusable powered-Koszul tensor tower, its canonical stage maps, and its data-bearing
derived-limit comparison live in `CategoryTheory.DerivedCategory.KoszulLimit`.

@stack 091Z
-/

@[expose] public section

/- Lemma 15.92.17 (Stacks `091Z`): the canonical comparison from `K` to a derived limit of the
powered-Koszul tensor tower is an isomorphism exactly when `K` is derived complete with respect to
`Ideal.span (Set.range f)`. -/
@[stacks 091Z]
#check @CategoryTheory.DerivedCategory.KoszulLimit.isDerivedComplete_iff_isIso

/- The owner exposes the tower, canonical stage maps, and normalized comparison as concrete data. -/
#check @CategoryTheory.DerivedCategory.KoszulLimit.tensorSystem
#check @CategoryTheory.DerivedCategory.KoszulLimit.toStage
#check @CategoryTheory.DerivedCategory.KoszulLimit.Comparison
#check @CategoryTheory.DerivedCategory.KoszulLimit.Comparison.isDerivedLimit
