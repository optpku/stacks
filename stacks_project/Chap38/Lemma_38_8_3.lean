/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.UniversallyInjective

open scoped TensorProduct

universe u v w z

/- Lemma 38.8.3: if every associated prime of `N ⊗[R] Q`, for every finite
`R`-module `Q`, avoids the extension of `I` to `S`, then the canonical map from `N`
to its `I`-adic completion is universally injective over `R`. Here `N ⊗[R] Q` is
the canonical left-action presentation of the source's `Q ⊗[R] N`. -/
@[stacks 05DL]
#check (AdicCompletion.of_universallyInjective_of_associatedPrimes :
  ∀ {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (I : Ideal R)
    (h_ass : ∀ (Q : Type z) [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
      (q : Ideal S), q ∈ associatedPrimesOfModule S (N ⊗[R] Q) →
        I.map (algebraMap R S) + q ≠ ⊤),
    LinearMap.UniversallyInjective.{u, w, w, z} (AdicCompletion.of I N))
