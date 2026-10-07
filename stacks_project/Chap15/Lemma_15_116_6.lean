module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Galois
import StacksCheckRecall

/-!
# Lemma 15.116.6

The reusable Galois action and transitivity theorem live in ReasLib.  This source-facing file is a
tagged recall block; its path retains the repository's legacy chapter numbering.

@stack 09EU
-/

@[expose] public section

/- Lemma 15.116.6: the right-factor action preserves the tensor nilradical and descends to the
reduced tensor product. -/
@[stacks 09EU "nilradical stability under the right-factor Galois action"]
#check @FieldExtension.TensorProduct.RightGalois.nilradicalStable
@[stacks 09EU "scalar compatibility of the reduced right-factor action"]
#check @FieldExtension.TensorProduct.RightGalois.quotientSMulCommClass

/- Lemma 15.116.6: for a finite normal extension, the induced Galois action is transitive on the
maximal ideals of the normalized reduced base change. -/
@[stacks 09EU "Galois transitivity on maximal ideals after reduced base change"]
#check @DVR.Field.BaseChange.Galois.exists_smul_eq_of_isMaximal
