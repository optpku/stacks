module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Rig-closed primes of Noetherian adic rings

A prime of a Noetherian adic ring is rig-closed when it satisfies the equivalent
conditions of Stacks lemma-rig-point, recorded here via Krull dimension 1 of the
quotient together with the condition that no ideal of definition is contained in
the prime.
-/

@[expose] public section

universe u v

open IsLocalRing

/-- A continuous homomorphism of linearly topologized rings sends the topological
nilradical of the source into the topological nilradical of the target. -/
theorem topologicalNilradical_map_le {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    topologicalNilradical A ≤ (topologicalNilradical B).comap φ :=
  sorry

namespace RingHom

/-- The homomorphism `A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B`
induced by a continuous ring homomorphism `φ : A →+* B`. -/
def topologicalNilradicalQuotient {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B :=
  Ideal.quotientMap (topologicalNilradical B) φ (topologicalNilradical_map_le φ hφ)

/-- The induced map on topological-nilradical quotients sends the class of `x` to
the class of `φ x`. -/
theorem topologicalNilradicalQuotient_apply {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hφ : Continuous φ) (x : A) :
    φ.topologicalNilradicalQuotient hφ (Ideal.Quotient.mk (topologicalNilradical A) x) =
      Ideal.Quotient.mk (topologicalNilradical B) (φ x) :=
  sorry

end RingHom

namespace Ideal

/-- A prime of a Noetherian adic ring is rig-closed when the quotient has Krull
dimension 1 and no ideal of definition is contained in the prime. -/
class IsRigClosed {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R) : Prop where
  /-- A rig-closed ideal is prime. -/
  isPrime : q.IsPrime
  /-- The quotient by a rig-closed ideal has Krull dimension 1. -/
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

/-- Rig-closedness unpacks as primeness, Krull dimension 1 of the quotient, and
the condition that no ideal of definition is contained in the prime. -/
theorem spec {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R) :
    IsRigClosed q ↔
      q.IsPrime ∧ ringKrullDim (R ⧸ q) = 1 ∧
        ∀ I : Ideal R, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q :=
  sorry

/-- The topological nilradical of the source is contained in the comap of the
maximal ideal of `B ⧸ q` along the composite `A →+* B ⧸ q`. -/
theorem topologicalNilradical_le_comap_maximalIdeal {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] :
    topologicalNilradical A ≤
      (maximalIdeal (B ⧸ q)).comap ((Quotient.mk q).comp φ) :=
  sorry

/-- The homomorphism `A ⧸ topologicalNilradical A →+* ResidueField (B ⧸ q)`
induced by a continuous ring homomorphism `φ : A →+* B` at a rig-closed prime
`q`. -/
def residueFieldHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] :
    A ⧸ topologicalNilradical A →+* ResidueField (B ⧸ q) :=
  Ideal.quotientMap (maximalIdeal (B ⧸ q)) ((Quotient.mk q).comp φ)
    (topologicalNilradical_le_comap_maximalIdeal φ hφ q)

/-- The induced residue-field map sends the class of `x` to the residue of the
class of `φ x` in `B ⧸ q`. -/
theorem residueFieldHom_apply {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] (x : A) :
    residueFieldHom φ hφ q (Quotient.mk (topologicalNilradical A) x) =
      residue (B ⧸ q) (Quotient.mk q (φ x)) :=
  sorry

end IsRigClosed

end Ideal

