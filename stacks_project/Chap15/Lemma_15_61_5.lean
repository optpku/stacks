/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat.BaseChange
import StacksCheckRecall

/-!
# Lemma 15.61.5

@stack 0DJD

Let `R → R'`, `R → A`, `R → B`, `R' → A'`, and `R' → B'` be the maps from
Lemma 15.61.3, with `R'` flat over `R`.  If the two normalized maps
`A ⊗[R] R' → A'` and `R' ⊗[R] B → B'` are flat, then for
`M : D(A)` the canonical comparison on homology of
`(M ⊗[A]^L (A ⊗[R] B))` after the induced map
`A ⊗[R] B → A' ⊗[R'] B'` is an isomorphism.

The explicit factor maps and the derived comparison are owned by the narrow
`FlatBaseChange` leaf; this file is the source-facing recall.
-/

@[expose] public section

@[stacks 0DJD "Lemma 15.61.5"]
#check @CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange.homologyComparison_isIso

@[stacks 0DJD "Lemma 15.61.5 tensor-product ring map"]
#check @CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange.productMap

@[stacks 0DJD "Lemma 15.61.5 left factor map"]
#check @CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange.leftBaseChangeMap

@[stacks 0DJD "Lemma 15.61.5 flatness bridge"]
#check @CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange.productMap_flat_of_baseChange
