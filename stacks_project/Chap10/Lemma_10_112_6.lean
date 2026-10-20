/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Fiber
import StacksCheckRecall

/-!
# Dimension Bound by a Local Fiber

@stack 00OM
-/

@[expose] public section

/- The quotient bridge identifies the local-fiber term below with the source
term `dim (S_q / pS_q)`; the map bridge identifies the extended ideal in the
localized rings. -/
@[stacks 00OM "quotient-localization bridge"]
#check @Algebra.Fiber.krullDim_quotientLocalizationAtPrime_eq

@[stacks 00OM "fiber maximal-ideal bridge"]
#check @Algebra.Fiber.map_maximalIdeal_eq

/- Lemma 10.112.6 (Stacks tag `00OM`): for primes `q` over `p` in a
homomorphism of Noetherian rings, `dim S_q ≤ dim R_p + dim (S_q / pS_q)`. -/
@[stacks 00OM]
#check @Algebra.Fiber.krullDim_localizationAtPrime_le_add
