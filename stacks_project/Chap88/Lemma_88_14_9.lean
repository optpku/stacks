/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed
public import stacks_project.Chap88.Lemma_88_14_9_Map

/-!
# Rig-closed primes after completed principal localization
-/

@[expose] public section

universe u v

open Ideal.IsRigClosed

/-- Lemma 88.14.9: let `φ : A →+* B` be an adic, topologically finite type
homomorphism of Noetherian adic rings, let `I` be an ideal of definition of
`A`, and let `q ⊂ B` be rig-closed. There exists `f : A` mapping to a unit in
`B ⧸ q` such that the completed principal localization square
`A → B → B_{{f}}` equals `A → A_{{f}} → B_{{f}}` via
`completedPrincipalLocalization.map φ I f`, the extended prime
`q' = q.map (completedPrincipalLocalization.of (I.map φ) (φ f))` equals
`q B_{{f}}`, and writing
`p' = q'.comap (completedPrincipalLocalization.map φ I f)`, one has
`ringKrullDim (A_{{f}} ⧸ p') = 1`, which is the property the proof identifies
with `p'` being rig-closed. -/
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
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (q : Ideal B) [q.IsRigClosed] :
    ∃ f : A, IsUnit (Ideal.Quotient.mk q (φ f)) ∧
      ∃ hf : IsUnit
          (residueFieldHom φ h_adic.continuous q
            (Ideal.Quotient.mk (topologicalNilradical A) f)),
        (Localization.awayLift (residueFieldHom φ h_adic.continuous q)
            (Ideal.Quotient.mk (topologicalNilradical A) f) hf).Finite :=
  sorry
