module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Étale defining quotients of adic ring homomorphisms
-/

@[expose] public section

universe u v

/-- Along an adic, topologically finite type, flat homomorphism of Noetherian
adic rings, the special fiber `A ⧸ I →+* B ⧸ I B` is étale for some
topological ideal of definition if and only if it is étale for every
topological ideal of definition. -/
theorem RingHom.etale_quotientMap_isIdealOfDefinition_iff_forall
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) :
    (∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale) ↔
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
        (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale :=
  sorry
