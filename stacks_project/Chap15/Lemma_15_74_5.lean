/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality

@[expose] public section

/-!
# Tensor-left derived internal-Hom comparison

Lemma 15.74.5 (0BYN): the tensor-left comparison, relative to an explicit fixed-right derived
tensor model, is owned by `InternalHom.TensorLeft`.

@stack 0BYN
-/

/- Lemma 15.74.5 (0BYN): the canonical tensor-left comparison and its functoriality. -/
@[stacks 0BYN "tensor-left derived internal-Hom comparison"]
#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf

#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf_natural_tensor
#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf_natural_target
#check @CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf_natural_source

#print axioms CategoryTheory.DerivedCategory.InternalHom.TensorLeft.comparisonOf
