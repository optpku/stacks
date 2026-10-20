/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Cotangent.Surjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.20.3
@stack 0E8M

The local-surjectivity conclusion is kept as the source-facing bridge.  The
Nakayama quotient criterion, residue-field map, and cotangent map are owned by
the underlying library APIs; the chapter file only records their use and the
textbook specialization.
-/

@[stacks 0E8M]
#check @IsLocalRing.CotangentSpace.algebraMap_surjective

#check @IsLocalRing.CotangentSpace.map
#check @IsLocalRing.CotangentSpace.map_maximalIdeal_eq

end
