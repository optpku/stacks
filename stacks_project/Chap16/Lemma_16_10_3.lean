/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
import ReasLib.RingTheory.RegularLocalRing.Parameters.Lifting
import ReasLib.RingTheory.Smooth.Resolution.Quotient
public import ReasLib.RingTheory.Smooth.Resolution.OverField

@[expose] public section

/- Lemma 16.10.3: over a field, regularity of the target local ring and
separability of its residue field resolve the map at a minimal transported
singular prime. The target is assumed Noetherian, not finite type. -/
@[stacks 07FE]
#check @AlgHom.ResolvableAtPrime.of_regularLocal

#check @Ideal.IsIdealOfDefinition.exists_maximalIdeal_pow_le
#check @Ideal.isIdealOfDefinition_map_atPrime
#check @PrimeSpectrum.Parameters.Lift.nonempty
#check @Module.IsTorsionStable.pow
#check @Ideal.finPrefixPowerSpan_pow
#check @RingTheory.Sequence.StableAnnihilators.pow
#check @AlgHom.ResolvableAtPrime.of_eighthPowerSpan
