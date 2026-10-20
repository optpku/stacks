module

public import ReasLib.FieldTheory.Separable.Conormal
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.140.4 [stacks 00TU]: canonical recall of the separable
residue-field conormal injectivity bridge.

@stack 00TU
-/

@[stacks 00TU]
#check @Algebra.IsSeparableOver.Conormal.residueField_injective
