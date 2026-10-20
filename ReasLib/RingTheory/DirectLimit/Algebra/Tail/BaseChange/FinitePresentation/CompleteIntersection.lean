module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.CompleteIntersection
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative global complete intersections over a cofinal tail

This source-facing adapter preserves the intrinsic ring-hom formulation while
using the canonical algebra structures selected by `Tail.stageAlgebra`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.CompleteIntersection

variable {I : Type u} [Preorder I] [IsDirectedOrder I]
variable (G : I → Type v) [∀ i, CommRing (G i)]
variable (f : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G (fun i j h ↦ f i j h)]
variable (i0 : I)
variable {B C : Type w} [CommRing B] [CommRing C]
variable [Algebra (G i0) B] [Algebra (G i0) C]

local notation "G∞" => Ring.DirectLimit G (fun i j h ↦ f i j h)

/-- Stacks tag `0C33` (1): relative global complete-intersection status of
the base change to the full direct limit is witnessed on a cofinal tail. -/
@[stacks 0C33 "relative global complete-intersection tail descent"]
theorem exists_stage
    (φ : B →ₐ[G i0] C)
    (hfinitePresentation : φ.FinitePresentation)
    (hcompleteIntersection :
      letI : Algebra (G i0) G∞ := Ring.DirectLimit.Algebra.stageAlgebra f i0
      RingHom.IsRelativeGlobalCompleteIntersection
        (Algebra.TensorProduct.map φ (AlgHom.id (G i0) G∞)).toRingHom) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      RingHom.IsRelativeGlobalCompleteIntersection
        (Algebra.TensorProduct.map φ (AlgHom.id (G i0) (G j.1))).toRingHom := sorry

end Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.CompleteIntersection
