/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed

/-!
# Contracting rig-closed primes along Jacobson special fibers
-/

@[expose] public section

universe u v

open Ideal.IsRigClosed

/-- Lemma 88.14.5: let `φ : A →+* B` be an adic, topologically finite type
homomorphism of Noetherian adic rings, and let `q ⊂ B` be rig-closed. If
`A ⧸ I` is Jacobson for some ideal of definition `I ⊂ A`, then `q.comap φ`
is rig-closed in `A`. -/
@[stacks 0GGC]
theorem Ideal.IsRigClosed.comap_of_isJacobsonRing {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    [IsJacobsonRing (A ⧸ I)] :
    (q.comap φ).IsRigClosed :=
  sorry
