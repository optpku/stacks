module

public import ReasLib.RingTheory.Topology.AdicStar.Composition

/-!
# Composition stability for continuous homomorphisms of adic-star rings

The composition-stability predicate, its characterization, and its application
lemma are supplied by the shared ring-theoretic owner.
-/

@[expose] public section

open TopologicalRing

universe u

/- Remark 87.21.13 (Variant for adic-star): composition stability for continuous
homomorphisms of adic-star rings. -/
#check (TopologicalRing.IsAdicStarRing.IsStableUnderComposition :
  (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop) → Prop)

#check (TopologicalRing.IsAdicStarRing.isStableUnderComposition_iff :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop),
    IsAdicStarRing.IsStableUnderComposition P ↔
      ∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]
      (φ : B →+* A) (ψ : C →+* B),
      Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))

#check (TopologicalRing.IsAdicStarRing.IsStableUnderComposition.comp :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicStarRing C],
    IsAdicStarRing.IsStableUnderComposition P →
    ∀ (φ : B →+* A) (ψ : C →+* B),
      Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))
