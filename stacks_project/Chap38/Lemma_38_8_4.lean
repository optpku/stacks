/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.UniversallyInjective
import StacksCheckRecall

universe u v w z

/- Lemma 38.8.4: if every prime in the relative assassin of the finite flat
`S`-module `N` avoids the extension of `I`, then the canonical map from `N` to
its `I`-adic completion is universally injective over `R`. -/
@[stacks 05DM] #check
  (AdicCompletion.of_universallyInjective_of_relativeAssassin :
    ∀ {R : Type u} {S : Type v} {N : Type w},
      [CommRing R] → [CommRing S] → [Algebra R S] →
      [AddCommGroup N] → [Module S N] → [Module R N] → [IsScalarTower R S N] →
      [IsNoetherianRing R] → [IsNoetherianRing S] →
      [Module.Finite S N] → [Module.Flat R N] → (I : Ideal R) →
      (∀ q : PrimeSpectrum S, q ∈ relativeAssassin R S N →
        I.map (algebraMap R S) + q.asIdeal ≠ ⊤) →
      LinearMap.UniversallyInjective.{u, w, w, z} (AdicCompletion.of I N))
