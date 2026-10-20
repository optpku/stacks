/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalizationAway.Map
public import ReasLib.RingTheory.Ideal.RigClosed
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Rig-closed primes after completed principal localization
-/

@[expose] public section

universe u v

open Ideal.IsRigClosed

/-- For an adic, topologically finite type homomorphism of Noetherian adic
rings and a rig-closed target prime, some source element is a unit modulo the
prime and makes the quotient by the contracted extended prime in the completed
principal localization have Krull dimension one, for any ideal of definition. -/
@[stacks 0GGG]
theorem Ideal.IsRigClosed.exists_away_ringKrullDim_quotient_eq_one
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (q : Ideal B) [q.IsRigClosed] :
    ∃ f : A, IsUnit (Ideal.Quotient.mk q (φ f)) ∧
      ringKrullDim
          (completedPrincipalLocalization I f ⧸
            (q.map (completedPrincipalLocalization.of (I.map φ) (φ f))).comap
              (completedPrincipalLocalization.map φ I f)) =
        1 :=
  sorry

/-- After inverting a suitable `f : A` that is a unit in `B ⧸ q`, the residue
field of `B ⧸ q` is finite over the principal localization of
`A ⧸ topologicalNilradical A` at the image of `f`. -/
theorem Ideal.IsRigClosed.exists_away_residueFieldHom_finite
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    ∃ f : A, IsUnit (Ideal.Quotient.mk q (φ f)) ∧
      ∃ hf : IsUnit
          (residueFieldHom φ h_adic.continuous q
            (Ideal.Quotient.mk (topologicalNilradical A) f)),
        (Localization.awayLift (residueFieldHom φ h_adic.continuous q)
            (Ideal.Quotient.mk (topologicalNilradical A) f) hf).Finite :=
  sorry
