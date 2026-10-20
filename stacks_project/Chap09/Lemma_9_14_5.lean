module

public import ReasLib.FieldTheory.PurelyInseparable.FiniteTower
import StacksCheckRecall

@[expose] public section

open FieldExtension

/- Lemma 9.14.5 (Tag 09HI): the finite purely inseparable tower construction is owned by
`FieldExtension.existsPthRootTowerOfFinitePurelyInseparable`; its degree-`p` simple-step input is
`FieldExtension.existsDegreePSimpleStepOfNontrivial`. -/
#check FieldExtension.IsPthRootTower
#check FieldExtension.existsDegreePSimpleStepOfNontrivial
@[stacks 09HI]
#check FieldExtension.existsPthRootTowerOfFinitePurelyInseparable
