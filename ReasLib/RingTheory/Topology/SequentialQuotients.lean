/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Order

/-!
# Sequential inverse limits of quotient rings

Compatible projections characterize the inverse limit, including its topology.
-/

@[expose] public section

universe u v

namespace TopologicalRing

/-- Projections exhibit a topological ring as the inverse limit of a descending sequence of
quotient rings with their discrete topologies. -/
def IsSequentialQuotientLimit {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace A] (J : ℕ → Ideal B) (hJ : ∀ n, J (n + 1) ≤ J n)
    (π : ∀ n, A →+* B ⧸ J n) : Prop :=
  (∀ n, (Ideal.Quotient.factor (hJ n)).comp (π (n + 1)) = π n) ∧
    (∀ x : ∀ n, B ⧸ J n,
      (∀ n, Ideal.Quotient.factor (hJ n) (x (n + 1)) = x n) →
        ∃! a : A, ∀ n, π n a = x n) ∧
    (inferInstance : TopologicalSpace A) =
      ⨅ n, TopologicalSpace.induced (π n) ⊥

namespace IsSequentialQuotientLimit

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A] [TopologicalSpace A]
    {J : ℕ → Ideal B} {hJ : ∀ n, J (n + 1) ≤ J n} {π : ∀ n, A →+* B ⧸ J n}

/-- In an inverse-limit realization, consecutive projections commute with quotient maps. -/
theorem compatible (h : IsSequentialQuotientLimit J hJ π) (n : ℕ) :
    (Ideal.Quotient.factor (hJ n)).comp (π (n + 1)) = π n :=
  h.1 n

/-- Every compatible quotient family has a unique lift to an inverse-limit realization. -/
theorem existsUnique (h : IsSequentialQuotientLimit J hJ π) (x : ∀ n, B ⧸ J n)
    (hx : ∀ n, Ideal.Quotient.factor (hJ n) (x (n + 1)) = x n) :
    ∃! a : A, ∀ n, π n a = x n :=
  h.2.1 x hx

/-- The topology of an inverse-limit realization is induced by its discrete quotient projections. -/
theorem topology_eq (h : IsSequentialQuotientLimit J hJ π) :
    (inferInstance : TopologicalSpace A) =
      ⨅ n, TopologicalSpace.induced (π n) ⊥ :=
  h.2.2

end IsSequentialQuotientLimit

end TopologicalRing
