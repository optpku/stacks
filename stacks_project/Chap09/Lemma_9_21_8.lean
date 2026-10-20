/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.Tower
import StacksCheckRecall

@[expose] public section

/- Lemma 9.21.8 (Tag 0BMH): the finite Galois-tower exact sequence is owned by the generic
`FieldExtension` restriction and normal-restriction API. -/
#check FieldExtension.galRestrictScalarsHom
#check FieldExtension.galRestrictScalarsHom_range_eq_restrictNormalHom_ker
@[stacks 0BMH]
#check FieldExtension.galoisGroupTowerShortExact
