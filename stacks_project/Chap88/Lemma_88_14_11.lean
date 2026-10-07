module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed

/-!
# Contraction of rig-closed primes along étale special fibers
-/

@[expose] public section

universe u v

/-- Lemma 88.14.11: an adic, topologically finite type, flat homomorphism of
Noetherian adic rings whose special fiber `A ⧸ I →+* B ⧸ I B` is étale for
some topological ideal of definition `I` of `A` sends a rig-closed prime `q`
of `B` whose contraction `q.comap φ` is also rig-closed to the equality of
extended ideals
`Ideal.map ((algebraMap B (Localization.AtPrime q)).comp φ) (q.comap φ)` and
`Ideal.map (algebraMap B (Localization.AtPrime q)) q`. -/
@[stacks 0GGI]
theorem Ideal.IsRigClosed.comap_map_eq_map_atPrime {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (h_etale : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale)
    (q : Ideal B) [q.IsRigClosed] [(q.comap φ).IsRigClosed] :
    Ideal.map ((algebraMap B (Localization.AtPrime q)).comp φ) (q.comap φ) =
      Ideal.map (algebraMap B (Localization.AtPrime q)) q :=
  sorry

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
