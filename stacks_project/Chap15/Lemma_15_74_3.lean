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
# Tensor-right derived internal-Hom comparison

Lemma 15.74.3 (0A67): the tensor-right comparison, relative to an explicit fixed-right derived
tensor model, is owned by `InternalHom.TensorRight`.

@stack 0A67
-/

/- Lemma 15.74.3 (0A67): the canonical tensor-right comparison and its functoriality. -/
@[stacks 0A67 "tensor-right derived internal-Hom comparison"]
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf

#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_spec
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_natural_tensor
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_natural_middle
#check @CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf_natural_target
#check @CategoryTheory.DerivedCategory.InternalHom.compOf_natural_target

#print axioms CategoryTheory.DerivedCategory.InternalHom.TensorRight.comparisonOf
