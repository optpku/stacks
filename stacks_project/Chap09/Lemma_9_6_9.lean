module

public import ReasLib.FieldTheory.TensorProduct.CommonOverfield
import StacksCheckRecall

@[expose] public section

/- Lemma 9.6.9 (Tag 0H7K): any two field extensions `E/k` and `F/k` embed into a common
overfield of `k`. -/
@[stacks 0H7K]
#check FieldExtension.existsCommonOverfield
