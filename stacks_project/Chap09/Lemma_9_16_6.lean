module

public import ReasLib.FieldTheory.Normal.TensorProduct
import StacksCheckRecall

@[expose] public section

/- Lemma 9.16.6 (Tag 0EXL): the finite tensor product of
`Cardinal.toNat (Field.sepDegree K L)` copies of `L` over `K` surjects onto the normal closure of
`L/K` inside `AlgebraicClosure L`. The source notation `[L : K]_s` is canonically
`Field.sepDegree K L`. -/
#check FieldExtension.piTensorProductToNormalClosure
#check FieldExtension.surjectivePiTensorProductToNormalClosure
@[stacks 0EXL]
#check FieldExtension.existsSurjectivePiTensorProductToNormalClosure
