/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic

/-!
# Lemma 87.6.4

A continuous adic homomorphism of pre-adic rings is taut.
-/

@[expose] public section

universe u v

namespace RingHom

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsPreadicRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsPreadicRing B]

/-- Lemma 87.6.4: Let `φ : A →+* B` be a continuous homomorphism between pre-adic
topological rings. If `φ` is adic, then `φ` is taut. -/
@[stacks 0GXC]
theorem IsAdicHom.isTaut {φ : A →+* B} (hφ_cont : Continuous φ) (hφ : φ.IsAdicHom) :
    φ.IsTaut := sorry

end RingHom
