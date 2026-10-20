/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Topology.Adic.Nilradical

/-!
# Rig-closed primes of Noetherian adic rings
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Ideal

/-- A prime of a Noetherian adic ring is rig-closed when its quotient has Krull
dimension one and no ideal of definition is contained in the prime. -/
class IsRigClosed {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R) : Prop where
  /-- A rig-closed ideal is prime. -/
  isPrime : q.IsPrime
  /-- The quotient by a rig-closed ideal has Krull dimension one. -/
  ringKrullDim_quotient_eq_one : ringKrullDim (R ⧸ q) = 1
  /-- No ideal of definition is contained in a rig-closed prime. -/
  not_le_of_isIdealOfDefinition :
    ∀ I : Ideal R, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

namespace IsRigClosed

/-- A rig-closed ideal is prime. -/
instance instIsPrime {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R)
    [h : IsRigClosed q] : q.IsPrime :=
  h.isPrime

/-- The quotient by a rig-closed ideal is a local ring. -/
instance instIsLocalRing_quotient {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R)
    [IsRigClosed q] : IsLocalRing (R ⧸ q) :=
  sorry

/-- Rig-closedness is equivalent to primeness, Krull dimension one of the
quotient, and avoidance of all ideals of definition. -/
theorem spec {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R) :
    IsRigClosed q ↔
      q.IsPrime ∧ ringKrullDim (R ⧸ q) = 1 ∧
        ∀ I : Ideal R, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q :=
  sorry

/-- The topological nilradical of the source lies in the inverse image of the
maximal ideal of the rig-closed quotient under the composite map. -/
theorem topologicalNilradical_le_comap_maximalIdeal {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] :
    topologicalNilradical A ≤
      (maximalIdeal (B ⧸ q)).comap ((Quotient.mk q).comp φ) :=
  sorry

/-- The homomorphism from the source reduction to the residue field of a
rig-closed quotient induced by a continuous homomorphism. -/
def residueFieldHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] :
    A ⧸ topologicalNilradical A →+* IsLocalRing.ResidueField (B ⧸ q) :=
  Ideal.quotientMap (maximalIdeal (B ⧸ q)) ((Quotient.mk q).comp φ)
    (topologicalNilradical_le_comap_maximalIdeal φ hφ q)

/-- The residue-field map sends the class of `x` to the residue of the
class of its image in the rig-closed quotient. -/
theorem residueFieldHom_apply {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] (x : A) :
    residueFieldHom φ hφ q (Quotient.mk (topologicalNilradical A) x) =
      residue (B ⧸ q) (Quotient.mk q (φ x)) :=
  sorry

/-- For a continuous map of Noetherian adic rings, finite type of the
induced map on reductions implies finite type of the induced map to the
residue field of a rig-closed quotient. -/
theorem residueFieldHom_finiteType {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ)
    (h_finiteType : (φ.topologicalNilradicalQuotient hφ).FiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (residueFieldHom φ hφ q).FiniteType :=
  sorry

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

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

/-- The quotient has Krull dimension one and some topological ideal of definition
is not contained in `q`. -/
def dimOneExistsNotLe (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q

/-- The quotient has Krull dimension one and no topological ideal of definition
is contained in `q`. -/
def dimOneForallNotLe (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧
    ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

/-- The quotient has Krull dimension one and its induced quotient topology is
not discrete. -/
def dimOneNontrivialTopology (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧ ¬ DiscreteTopology (A ⧸ q)

/-- The quotient is a one-dimensional Noetherian complete local domain whose
maximal ideal is the radical of the image of every topological ideal of definition. -/
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

/-- Rig-closedness is equivalent to primeness together with dimension one and
existence of a topological ideal of definition not contained in the prime. -/
theorem iff_dimOneExistsNotLe (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneExistsNotLe q :=
  sorry

/-- Rig-closedness is equivalent to primeness together with dimension one and
avoidance of every topological ideal of definition. -/
theorem iff_dimOneForallNotLe (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneForallNotLe q :=
  sorry

/-- Rig-closedness is equivalent to primeness together with dimension one and
nondiscreteness of the induced topology on the quotient. -/
theorem iff_nontrivialTopology (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneNontrivialTopology q :=
  sorry

/-- Rig-closedness is equivalent to the quotient being a one-dimensional
Noetherian complete local domain whose maximal ideal is the radical of the
image of every topological ideal of definition. -/
theorem iff_isCompleteLocalDomain (q : Ideal A) :
    IsRigClosed q ↔ isCompleteLocalDomain q :=
  sorry

/-- The complete-local-domain condition is equivalent to requiring each
radical image of an ideal of definition to equal the unique maximal ideal. -/
theorem isCompleteLocalDomain_iff (q : Ideal A) :
    isCompleteLocalDomain q ↔
      IsCompleteLocalRing (A ⧸ q) ∧ IsDomain (A ⧸ q) ∧
        IsNoetherianRing (A ⧸ q) ∧ ringKrullDim (A ⧸ q) = 1 ∧
        ∀ [IsCompleteLocalRing (A ⧸ q)] (I : Ideal A),
          TopologicalRing.Ideal.IsIdealOfDefinition I →
            (I.map (Ideal.Quotient.mk q)).radical = maximalIdeal (A ⧸ q) :=
  sorry

/-- The quotient by a rig-closed prime is a complete local ring. -/
instance isCompleteLocalRing_quotient (q : Ideal A) [IsRigClosed q] :
    IsCompleteLocalRing (A ⧸ q) :=
  sorry

end IsRigClosed

end Ideal

namespace PrimeSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- A point of the prime spectrum is rig-closed when its underlying ideal is rig-closed. -/
abbrev IsRigClosed (q : PrimeSpectrum A) : Prop :=
  q.asIdeal.IsRigClosed

open Ideal.IsRigClosed

/-- For a prime of a Noetherian adic ring, maximal avoidance, relative
closedness, dimension one with ideal avoidance, nondiscrete quotient topology,
and the complete-local-domain condition give eight equivalent characterizations. -/
theorem isRigClosed_tfae (q : PrimeSpectrum A) :
    List.TFAE
      [ existsMaximal q.asIdeal, existsClosedPoint q
      , forallMaximal q.asIdeal, forallClosedPoint q
      , dimOneExistsNotLe q.asIdeal, dimOneForallNotLe q.asIdeal
      , dimOneNontrivialTopology q.asIdeal
      , isCompleteLocalDomain q.asIdeal ] :=
  sorry

end PrimeSpectrum
