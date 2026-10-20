module

public import ReasLib.RingTheory.Topology.Adic.Etale
public import ReasLib.RingTheory.Ideal.RigClosed.Etale
import StacksCheckRecall

/-!
# Contraction of rig-closed primes along étale special fibers
-/

@[expose] public section

universe u v

/- Lemma 88.14.11: an adic, topologically finite type, flat homomorphism of
Noetherian adic rings whose special fiber `A ⧸ I →+* B ⧸ I B` is étale for
some topological ideal of definition `I` of `A` sends a rig-closed prime `q`
of `B` whose contraction `q.comap φ` is also rig-closed to the equality of
extended ideals
`Ideal.map ((algebraMap B (Localization.AtPrime q)).comp φ) (q.comap φ)` and
`Ideal.map (algebraMap B (Localization.AtPrime q)) q`. -/
@[stacks 0GGI]
#check (Ideal.IsRigClosed.comap_map_eq_map_atPrime :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (h_etale : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale)
    (q : Ideal B) [q.IsRigClosed] [(q.comap φ).IsRigClosed],
    Ideal.map ((algebraMap B (Localization.AtPrime q)).comp φ) (q.comap φ) =
      Ideal.map (algebraMap B (Localization.AtPrime q)) q)

/- Along an adic, topologically finite type, flat homomorphism of Noetherian
adic rings, the special fiber `A ⧸ I →+* B ⧸ I B` is étale for some
topological ideal of definition if and only if it is étale for every
topological ideal of definition. -/
#check (RingHom.etale_quotientMap_isIdealOfDefinition_iff_forall :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat),
    (∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale) ↔
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
        (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale)
