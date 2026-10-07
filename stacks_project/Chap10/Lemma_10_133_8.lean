module

public import ReasLib.Algebra.Module.PrincipalParts.TensorProduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.133.8

@stack 0H8Z

Lemma 10.133.8 (Tag 0H8Z): principal parts commute with the tensor-product
base change `S → S ⊗[R] T`.  The canonical comparison map is a base change,
and its scalar extension is bijective.

The reusable construction is owned by
`PrincipalParts.BaseChange.TensorProduct`; this source file records the
textbook label without retaining a chapter-local tensor-presentation model.
-/

@[stacks 0H8Z "principal-parts tensor base change"]
#check @PrincipalParts.BaseChange.TensorProduct.isBaseChange

@[stacks 0H8Z "principal-parts tensor lift bijectivity"]
#check @PrincipalParts.BaseChange.TensorProduct.lift_bijective
