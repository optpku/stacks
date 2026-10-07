module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Lemma_88_15_8_RigFlat

/-!
# Descent of rig-flatness along an étale special fiber
-/

@[expose] public section

universe u

namespace RingHom.RigFlat

/-- Lemma 88.15.7: in a commutative square of arrows of `WAdm^{Noeth}` that
are all adic and topologically of finite type, if the horizontal maps
`A →+* A'` and `B →+* B'` are flat, `I ⊂ A` is an ideal of definition, the
left vertical map `φ` is rig-flat, and the special fiber
`A ⧸ I →+* A' ⧸ I.map fA` is étale, then the right vertical map `φ'` is
rig-flat. -/
@[stacks 0GGS]
theorem of_etale_specialFiber_square
    {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing A'] [TopologicalRing.IsAdicRing B']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing A'] [IsNoetherianRing B']
    (φ : A →+* B) (φ' : A' →+* B') (fA : A →+* A') (fB : B →+* B')
    (h_comm : φ'.comp fA = fB.comp φ)
    (hφ_adic : φ.IsAdicHom) (hφ'_adic : φ'.IsAdicHom)
    (hfA_adic : fA.IsAdicHom) (hfB_adic : fB.IsAdicHom)
    (hφ_tft : φ.TopologicallyFiniteType) (hφ'_tft : φ'.TopologicallyFiniteType)
    (hfA_tft : fA.TopologicallyFiniteType) (hfB_tft : fB.TopologicallyFiniteType)
    (hfA_flat : fA.Flat) (hfB_flat : fB.Flat) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (hφ : RigFlat φ)
    (h_etale : (Ideal.quotientMap (I.map fA) fA Ideal.le_comap_map).Etale) :
    RigFlat φ' :=
  sorry

end RingHom.RigFlat
