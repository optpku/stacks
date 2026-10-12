/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed

/-!
# Residue fields of rig-closed primes in a relative setting
-/

@[expose] public section

universe u v

open Ideal.IsRigClosed

/-- Lemma 88.14.3: let `φ : A →+* B` be a continuous homomorphism of Noetherian
adic rings, and write `a = topologicalNilradical A` and
`b = topologicalNilradical B`. If `A ⧸ a →+* B ⧸ b` is of finite type and
`q ⊂ B` is rig-closed, then the residue field of the local ring `B ⧸ q` is a
finite-type `A ⧸ a`-algebra. -/
@[stacks 0GGA]
theorem Ideal.IsRigClosed.residueFieldHom_finiteType {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ)
    (h_finiteType : (φ.topologicalNilradicalQuotient hφ).FiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (residueFieldHom φ hφ q).FiniteType :=
  sorry
