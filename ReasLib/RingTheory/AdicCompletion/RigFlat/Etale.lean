/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigFlat
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Rig-flatness along an étale special fiber
-/

@[expose] public section

universe u

namespace RingHom.RigFlat

/-- In a commutative square of adic, topologically finite-type homomorphisms of
adic Noetherian rings with flat horizontal maps, rig-flatness of the left
vertical map implies rig-flatness of the right vertical map when the induced
map modulo an ideal of definition is étale. -/
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
