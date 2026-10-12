/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Lemma 87.5.4

Composition of taut homomorphisms of linearly topologized rings is taut.
-/

@[expose] public section

universe u v w

namespace RingHom

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- Lemma 87.5.4: Let `A → B` and `B → C` be continuous homomorphisms of linearly
topologized rings. If `A → B` and `B → C` are taut, then `A → C` is taut. -/
@[stacks 0GX3]
theorem IsTaut.comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (hφ : φ.IsTaut) (hψ : ψ.IsTaut) :
    (ψ.comp φ).IsTaut := sorry

end RingHom
