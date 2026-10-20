/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
