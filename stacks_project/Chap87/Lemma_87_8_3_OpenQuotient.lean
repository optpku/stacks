/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Faithfully flat open quotients of taut ring maps

In the standing situation of Stacks section 87.8, a continuous taut homomorphism
`φ : A →+* B` of linearly topologized rings is assumed to induce a faithfully
flat map `A ⧸ I →+* B ⧸ J` for every open ideal `I` of `A`, where `J` is the
closure of `Ideal.map φ I`.
-/

@[expose] public section

universe u v

namespace RingHom

/-- The source ideal is contained in the comap of the closure of its extension. -/
theorem le_comap_closure_map {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] (φ : A →+* B) (I : Ideal A) :
    I ≤ (Ideal.map φ I).closure.comap φ :=
  sorry

/-- A homomorphism of linearly topologized rings has faithfully flat open quotients
if for every open ideal `I` of the source, writing `J` for the closure of
`Ideal.map φ I`, the induced map `A ⧸ I →+* B ⧸ J` is faithfully flat. -/
def FaithfullyFlatOpenQuotients {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, IsOpen (I : Set A) →
    (Ideal.quotientMap (Ideal.map φ I).closure φ (le_comap_closure_map φ I)).FaithfullyFlat

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- Faithfully flat open quotients means that every induced quotient map along the
closure of an open ideal's extension is faithfully flat, for any proof of the
comap inequality. -/
theorem faithfullyFlatOpenQuotients_iff (φ : A →+* B) :
    φ.FaithfullyFlatOpenQuotients ↔
      ∀ I : Ideal A, IsOpen (I : Set A) →
        ∀ h : I ≤ (Ideal.map φ I).closure.comap φ,
          (Ideal.quotientMap (Ideal.map φ I).closure φ h).FaithfullyFlat :=
  sorry

namespace FaithfullyFlatOpenQuotients

/-- The induced map `A ⧸ I →+* B ⧸ (Ideal.map φ I).closure` is faithfully flat. -/
theorem faithfullyFlat {φ : A →+* B} (hφ : φ.FaithfullyFlatOpenQuotients) {I : Ideal A}
    (hI : IsOpen (I : Set A)) :
    (Ideal.quotientMap (Ideal.map φ I).closure φ (le_comap_closure_map φ I)).FaithfullyFlat :=
  sorry

end FaithfullyFlatOpenQuotients

end RingHom
