module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.RigClosed.LocalizationAway

@[expose] public section

universe u v

open Ideal.IsRigClosed

/- Lemma 88.14.9: a rig-closed target prime becomes rig-closed over a suitable
completed principal localization of the source. -/
@[stacks 0GGG] #check (Ideal.IsRigClosed.exists_away_ringKrullDim_quotient_eq_one :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (q : Ideal B) [q.IsRigClosed],
    ∃ f : A, IsUnit (Ideal.Quotient.mk q (φ f)) ∧
      ringKrullDim
          (completedPrincipalLocalization I f ⧸
            (q.map (completedPrincipalLocalization.of (I.map φ) (φ f))).comap
              (completedPrincipalLocalization.map φ I f)) =
        1)

/- Finiteness of the canonical localized residue-field homomorphism. -/
#check (Ideal.IsRigClosed.exists_away_residueFieldHom_finite :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed],
    ∃ f : A, IsUnit (Ideal.Quotient.mk q (φ f)) ∧
      ∃ hf : IsUnit
          (residueFieldHom φ h_adic.continuous q
            (Ideal.Quotient.mk (topologicalNilradical A) f)),
        (Localization.awayLift (residueFieldHom φ h_adic.continuous q)
            (Ideal.Quotient.mk (topologicalNilradical A) f) hf).Finite)
