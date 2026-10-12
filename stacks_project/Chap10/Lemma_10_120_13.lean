/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.PrincipalIdealDomain
import StacksCheckRecall

/-!
# Principal ideal domains are unique factorization domains

@stack 034V
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- Lemma 10.120.13 (Stacks `034V`): a principal ideal domain has Mathlib's canonical unique
factorization instance. -/
@[stacks 034V]
#check (PrincipalIdealRing.to_uniqueFactorizationMonoid :
  UniqueFactorizationMonoid R)
