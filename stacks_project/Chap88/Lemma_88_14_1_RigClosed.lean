/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Rig-closed primes of Noetherian adic rings

A prime of a Noetherian adic topological ring is rig-closed when the quotient
has Krull dimension 1 and no topological ideal of definition is contained in
the prime. Stacks lemma-rig-point records eight equivalent characterizations
of this property.
-/

@[expose] public section

universe u

open IsLocalRing

namespace Ideal

/-- A prime of a Noetherian adic topological ring is rig-closed when the
quotient has Krull dimension 1 and no topological ideal of definition is
contained in the prime. -/
@[mk_iff]
class IsRigClosed {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] (q : Ideal A) : Prop where
  /-- A rig-closed ideal is prime. -/
  isPrime : q.IsPrime
  /-- The quotient by a rig-closed ideal has Krull dimension 1. -/
  ringKrullDim_quotient_eq_one : ringKrullDim (A ⧸ q) = 1
  /-- No topological ideal of definition is contained in a rig-closed prime. -/
  not_le_of_isIdealOfDefinition :
    ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

namespace IsRigClosed

/-- A rig-closed ideal is prime. -/
instance instIsPrime (q : Ideal A) [h : IsRigClosed q] : q.IsPrime :=
  h.isPrime

/-- The quotient by a rig-closed ideal is a local ring. -/
instance instIsLocalRing_quotient (q : Ideal A) [IsRigClosed q] :
    IsLocalRing (A ⧸ q) :=
  sorry

/-- Rig-closedness unpacks as primeness, Krull dimension 1 of the quotient, and
avoidance of every topological ideal of definition. -/
theorem spec (q : Ideal A) :
    IsRigClosed q ↔
      q.IsPrime ∧ ringKrullDim (A ⧸ q) = 1 ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q :=
  sorry

/-- Some topological ideal of definition is not contained in `q`, and `q` is
maximal among primes with this property. -/
def existsMaximal (q : Ideal A) : Prop :=
  ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
    Maximal (fun r : Ideal A ↦ r.IsPrime ∧ ¬ I ≤ r) q

/-- For some topological ideal of definition `I`, the prime `p` is a closed
point of `PrimeSpectrum A` minus `zeroLocus I`. -/
def existsClosedPoint (p : PrimeSpectrum A) : Prop :=
  ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
    p ∉ PrimeSpectrum.zeroLocus I ∧
      closure {p} ∩ (PrimeSpectrum.zeroLocus I)ᶜ = {p}

/-- Every topological ideal of definition is not contained in `q`, and `q` is
maximal among primes with this property. -/
def forallMaximal (q : Ideal A) : Prop :=
  ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
    Maximal (fun r : Ideal A ↦ r.IsPrime ∧ ¬ I ≤ r) q

/-- For every topological ideal of definition `I`, the prime `p` is a closed
point of `PrimeSpectrum A` minus `zeroLocus I`. -/
def forallClosedPoint (p : PrimeSpectrum A) : Prop :=
  ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
    p ∉ PrimeSpectrum.zeroLocus I ∧
      closure {p} ∩ (PrimeSpectrum.zeroLocus I)ᶜ = {p}

/-- The quotient has Krull dimension 1 and some topological ideal of definition
is not contained in `q`. -/
def dimOneExistsNotLe (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q

/-- The quotient has Krull dimension 1 and no topological ideal of definition
is contained in `q`. -/
def dimOneForallNotLe (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧
    ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

/-- The quotient has Krull dimension 1 and its induced quotient topology is
not discrete. -/
def dimOneNontrivialTopology (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧ ¬ DiscreteTopology (A ⧸ q)

/-- `A ⧸ q` is a 1-dimensional Noetherian complete local domain whose maximal
ideal is the radical of the image of any topological ideal of definition of
`A`. -/
def isCompleteLocalDomain (q : Ideal A) : Prop :=
  IsCompleteLocalRing (A ⧸ q) ∧ IsDomain (A ⧸ q) ∧ IsNoetherianRing (A ⧸ q) ∧
    ringKrullDim (A ⧸ q) = 1 ∧
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
        (I.map (Ideal.Quotient.mk q)).radical.IsMaximal

/-- Rig-closedness is equivalent to maximality among primes avoiding some
topological ideal of definition. -/
theorem iff_existsMaximal (q : Ideal A) :
    IsRigClosed q ↔ existsMaximal q :=
  sorry

/-- Rig-closedness is equivalent to being a closed point of
`PrimeSpectrum A` minus `zeroLocus I` for some topological ideal of
definition `I`. -/
theorem iff_existsClosedPoint (p : PrimeSpectrum A) :
    IsRigClosed p.asIdeal ↔ existsClosedPoint p :=
  sorry

/-- Rig-closedness is equivalent to maximality among primes avoiding every
topological ideal of definition. -/
theorem iff_forallMaximal (q : Ideal A) :
    IsRigClosed q ↔ forallMaximal q :=
  sorry

/-- Rig-closedness is equivalent to being a closed point of
`PrimeSpectrum A` minus `zeroLocus I` for every topological ideal of
definition `I`. -/
theorem iff_forallClosedPoint (p : PrimeSpectrum A) :
    IsRigClosed p.asIdeal ↔ forallClosedPoint p :=
  sorry

/-- Rig-closedness is equivalent to primeness together with dimension 1 and
existence of a topological ideal of definition not contained in the prime. -/
theorem iff_dimOneExistsNotLe (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneExistsNotLe q :=
  sorry

/-- Rig-closedness is equivalent to primeness together with dimension 1 and
avoidance of every topological ideal of definition. -/
theorem iff_dimOneForallNotLe (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneForallNotLe q :=
  sorry

/-- Rig-closedness is equivalent to primeness together with dimension 1 and
nontrivial induced topology on the quotient. -/
theorem iff_nontrivialTopology (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneNontrivialTopology q :=
  sorry

/-- Rig-closedness is equivalent to the quotient being a 1-dimensional
Noetherian complete local domain whose maximal ideal is the radical of the
image of any topological ideal of definition. -/
theorem iff_isCompleteLocalDomain (q : Ideal A) :
    IsRigClosed q ↔ isCompleteLocalDomain q :=
  sorry

/-- Unfolding of `isCompleteLocalDomain` with the radical of the image equal to
the maximal ideal, equivalently the algebraic local-ring ideal-of-definition
condition on that image. -/
theorem isCompleteLocalDomain_iff (q : Ideal A) :
    isCompleteLocalDomain q ↔
      IsCompleteLocalRing (A ⧸ q) ∧ IsDomain (A ⧸ q) ∧
        IsNoetherianRing (A ⧸ q) ∧ ringKrullDim (A ⧸ q) = 1 ∧
        ∀ [IsCompleteLocalRing (A ⧸ q)] (I : Ideal A),
          TopologicalRing.Ideal.IsIdealOfDefinition I →
            (I.map (Ideal.Quotient.mk q)).radical = maximalIdeal (A ⧸ q) :=
  sorry

/-- The quotient by a rig-closed prime is a complete local ring. -/
theorem isCompleteLocalRing_quotient (q : Ideal A) [IsRigClosed q] :
    IsCompleteLocalRing (A ⧸ q) :=
  sorry

end IsRigClosed

end Ideal

namespace PrimeSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- A point of `PrimeSpectrum A` is rig-closed when its underlying ideal is. -/
abbrev IsRigClosed (q : PrimeSpectrum A) : Prop :=
  q.asIdeal.IsRigClosed

/-- Spectrum-level rig-closedness is the unbundled class on the underlying
ideal. -/
theorem isRigClosed_iff (q : PrimeSpectrum A) :
    IsRigClosed q ↔ q.asIdeal.IsRigClosed :=
  sorry

end PrimeSpectrum
