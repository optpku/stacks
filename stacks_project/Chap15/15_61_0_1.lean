/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout.Comparison

@[expose] public section

/-!
# Derived base-change comparison

15.61.0.1 (065Z): the comparison
`K \otimes_A^L A' \longrightarrow K \otimes_R^L (A' \otimes_A R)` is the object component of
the canonical derived comparison around the tensor-product pushout square.  Its reusable owner is
`ModuleCat.Pushout.DerivedExtension.TensorProduct`.

@stack 065Z
-/

@[stacks 065Z "derived base-change comparison"]
#check @CategoryTheory.ModuleCat.Pushout.DerivedExtension.TensorProduct.comparison

#check @CategoryTheory.ModuleCat.Pushout.DerivedExtension.TensorProduct.comparisonApp
#check @CategoryTheory.ModuleCat.Pushout.DerivedExtension.comparison
#check @CategoryTheory.ModuleCat.Pushout.DerivedExtension.routeIso

#print axioms CategoryTheory.ModuleCat.Pushout.DerivedExtension.TensorProduct.comparison
