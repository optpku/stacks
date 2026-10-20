/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.PowerGeneration
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.6

The source is generation as a field extension, so its primary owner uses
`IntermediateField.adjoin`, not a ring closure.  A separate bridge provides
the ring-level power-generation formulation where it is useful.

@stack 0BR9
-/

/- Lemma 10.46.6 (Tag 0BR9): field generation by prime-power/scalar-image elements is
equivalent to triviality or purely inseparable characteristic-`p` extension. -/
@[stacks 0BR9]
#check @FieldExtension.PowerGeneration.iff_surjective_or_charP_isPurelyInseparable

#check @FieldExtension.PowerGeneration.IsGenerated
#check @FieldExtension.PowerGeneration.isGenerated_iff_ringHom
#check @RingHom.PowerGeneration.IsGenerated
