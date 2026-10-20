/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.UniqueFactorizationDomain.Nagata
import StacksCheckRecall

/-!
# Nagata's criterion for factoriality

@stack 0AFU
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A] [IsDomain A] {S : Submonoid A}

/- Lemma 10.120.7 (Stacks `0AFU`) is a source-facing recall of the neutral
Nagata criterion.  The reusable owner is
`UniqueFactorizationMonoid.iff_localization_of_primeGenerated`; its
prime/irreducible localization bridges are exposed in
`UniqueFactorizationMonoid.Localization`. -/
@[stacks 0AFU]
#check @UniqueFactorizationMonoid.iff_localization_of_primeGenerated

@[stacks 0AFU "irreducible localization bridge"]
#check @UniqueFactorizationMonoid.Localization.irreducible_or_isUnit_of_irreducible

@[stacks 0AFU "prime localization bridge"]
#check @UniqueFactorizationMonoid.Localization.prime_iff_prime_or_isUnit_of_irreducible
