/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import StacksCheckRecall

/-!
# Unique Factorization Domains

@stack 034S
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R] [IsDomain R]

/- Definition 10.120.4 (Stacks `034S`): the source UFD condition is Mathlib's canonical
`UniqueFactorizationMonoid` owner in a domain. -/
@[stacks 034S]
#check (UniqueFactorizationMonoid R : Prop)

@[stacks 034S "prime factor existence"]
#check @UniqueFactorizationMonoid.exists_prime_factors
@[stacks 034S "factorization uniqueness"]
#check @UniqueFactorizationMonoid.factors_unique
