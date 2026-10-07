module

public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Rig-closed primes of Noetherian adic rings

A prime of a Noetherian adic topological ring is rig-closed when the quotient
has Krull dimension 1 and some ideal of definition is not contained in it.
This is the form of lemma-rig-point (5) used to name rig-closed hypotheses.
-/

@[expose] public section

universe u

namespace TopologicalRing.Ideal

/-- A prime of a Noetherian adic topological ring is rig-closed when the
quotient has Krull dimension 1 and some ideal of definition is not contained
in it. -/
class IsRigClosed {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] (q : Ideal A) : Prop where
  /-- A rig-closed ideal is prime. -/
  isPrime : q.IsPrime
  /-- The quotient by a rig-closed prime has Krull dimension 1. -/
  ringKrullDim_quotient : ringKrullDim (A ⧸ q) = 1
  /-- Some ideal of definition is not contained in a rig-closed prime. -/
  exists_isIdealOfDefinition_not_le :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ¬ I ≤ q

namespace IsRigClosed

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- A rig-closed ideal is prime. -/
instance instIsPrime {q : Ideal A} [h : IsRigClosed q] : q.IsPrime :=
  h.isPrime

/-- Rig-closedness unpacks as primeness, Krull dimension 1 of the quotient, and
the existence of an ideal of definition not contained in the prime. -/
theorem iff (q : Ideal A) :
    IsRigClosed q ↔
      q.IsPrime ∧ ringKrullDim (A ⧸ q) = 1 ∧
        ∃ I : Ideal A, IsIdealOfDefinition I ∧ ¬ I ≤ q :=
  sorry

/-- Every ideal of definition fails to be contained in a rig-closed prime. -/
theorem not_le_forall_isIdealOfDefinition {q : Ideal A} [IsRigClosed q]
    (I : Ideal A) (hI : IsIdealOfDefinition I) : ¬ I ≤ q :=
  sorry

end IsRigClosed

end TopologicalRing.Ideal
