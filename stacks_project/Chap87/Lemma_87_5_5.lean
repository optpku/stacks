module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Lemma 87.5.5

If a composite of continuous homomorphisms of linearly topologized rings is taut, then
the second homomorphism is taut.
-/

@[expose] public section

universe u v w

namespace RingHom

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- Lemma 87.5.5: Let `A → B` and `B → C` be continuous homomorphisms of linearly
topologized rings. If `A → C` is taut, then `B → C` is taut. -/
@[stacks 0GX4]
theorem IsTaut.of_comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (h : (ψ.comp φ).IsTaut) : ψ.IsTaut := sorry

end RingHom
