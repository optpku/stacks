module

public import Mathlib.FieldTheory.PrimitiveElement
import StacksCheckRecall

@[expose] public section

/- Lemma 9.19.1 (Primitive element): a finite field extension has a primitive element exactly
when its lattice of intermediate fields is finite; finite separable extensions satisfy this
criterion. -/
@[stacks 030N]
#check Field.exists_primitive_element_iff_finite_intermediateField
#check Field.finite_intermediateField_of_exists_primitive_element
#check Field.exists_primitive_element
