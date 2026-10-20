/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent.Idempotent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.32.6
@stack 00J9
-/

/- Lemma 10.32.6 (Tag 00J9): quotienting by a locally nilpotent ideal induces a bijection on
idempotents. -/
@[stacks 00J9]
#check @Ideal.IsLocallyNilpotent.quotient_idempotentMap_bijective

/- The reusable map-level unique-lifting form of Lemma 10.32.6. -/
@[stacks 00J9]
#check @RingHom.existsUnique_idempotent_lift_of_ker_isLocallyNilpotent

/- The injective half of the map-level idempotent API. -/
@[stacks 00J9]
#check @RingHom.idempotentMap_injective_of_ker_isLocallyNilpotent

/- The surjective half of the map-level idempotent API. -/
@[stacks 00J9]
#check @RingHom.idempotentMap_surjective_of_surjective_of_ker_isLocallyNilpotent

/- The map-level bijection specializing to the quotient statement above. -/
@[stacks 00J9]
#check @RingHom.idempotentMap_bijective_of_surjective_of_ker_isLocallyNilpotent

/- The pointwise unique-lift form of the quotient statement. -/
@[stacks 00J9]
#check @Ideal.IsLocallyNilpotent.existsUnique_idempotent_lift_quotient
