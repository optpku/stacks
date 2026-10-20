/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RestrictedPowerSeries.RigClosed
import StacksCheckRecall

/-!
# Completions of localizations at rig-closed primes of restricted power series
-/

@[expose] public section

universe u

/- Lemma 88.14.10: if `A` is a Noetherian adic topological ring, `q` is a
rig-closed prime of `RestrictedPowerSeries (Fin n) A`, and
`q.comap (algebraMap A (RestrictedPowerSeries (Fin n) A))` is also rig-closed,
then the completed local map of `ofPolynomial` is an isomorphism of completed
local rings. -/
@[stacks 0GGH] #check (RestrictedPowerSeries.completedLocalMap_bijective :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] (n : ℕ)
    (q : Ideal (RestrictedPowerSeries (Fin n) A))
    [q.IsRigClosed]
    [(q.comap (algebraMap A (RestrictedPowerSeries (Fin n) A))).IsRigClosed],
    Function.Bijective
      (RingHom.completedLocalMap
        (RestrictedPowerSeries.ofPolynomial : MvPolynomial (Fin n) A →ₐ[A]
          RestrictedPowerSeries (Fin n) A).toRingHom
        ⟨q, inferInstance⟩))
