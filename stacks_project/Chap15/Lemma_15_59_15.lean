module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Associativity
import StacksCheckRecall

@[expose] public section

/-!
# Associativity of the derived tensor product

Lemma 15.59.15 (0BYJ): relative to an explicit ambient fixed-right model, derived tensor product
has an associativity isomorphism functorial in all three complexes. The reusable owner is
`CategoryTheory.DerivedCategory.DerivedTensor.Right`.

@stack 0BYJ
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open scoped DerivedTensorProduct

universe u

namespace CategoryTheory

variable {R : Type u} [CommRing R]

variable [MonoidalCategory (DerivedCategory (ModuleCat R))]
variable [DerivedTensor.Right.Has (C := ModuleCat R)]

/- Lemma 15.59.15 (0BYJ): the canonical model-parametrized comparison and its naturality in
each of the three derived-complex variables. -/
@[stacks 0BYJ "fixed-right derived tensor functor associativity"]
#check DerivedTensor.Right.tensorAssoc
@[stacks 0BYJ "objectwise fixed-right derived tensor associativity"]
#check DerivedTensor.Right.assoc
@[stacks 0BYJ "left naturality of derived tensor associativity"]
#check DerivedTensor.Right.assoc_hom_naturality
@[stacks 0BYJ "inverse left naturality of derived tensor associativity"]
#check DerivedTensor.Right.assoc_inv_naturality
@[stacks 0BYJ "middle naturality of derived tensor associativity"]
#check DerivedTensor.Right.assoc_hom_naturality_middle
@[stacks 0BYJ "inverse middle naturality of derived tensor associativity"]
#check DerivedTensor.Right.assoc_inv_naturality_middle
@[stacks 0BYJ "right naturality of derived tensor associativity"]
#check DerivedTensor.Right.assoc_hom_naturality_right
@[stacks 0BYJ "inverse right naturality of derived tensor associativity"]
#check DerivedTensor.Right.assoc_inv_naturality_right

#print axioms DerivedTensor.Right.tensorAssoc
#print axioms DerivedTensor.Right.assoc

end CategoryTheory
