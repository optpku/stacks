module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.Syntomic
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Syntomicity over a cofinal tail

This is the source-facing tail adapter for the fixed-base syntomic descent
theorem; the property itself remains the intrinsic `RingHom.Syntomic` one.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Syntomic

variable {I : Type u} [Preorder I] [IsDirectedOrder I]
variable (G : I → Type v) [∀ i, CommRing (G i)]
variable (f : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G (fun i j h ↦ f i j h)]
variable (i0 : I)
variable {B C : Type w} [CommRing B] [CommRing C]
variable [Algebra (G i0) B] [Algebra (G i0) C]

local notation "G∞" => Ring.DirectLimit G (fun i j h ↦ f i j h)

/-- Stacks tag `0C33` (2): syntomicity of the base change to the full direct
limit is witnessed on a cofinal tail. -/
@[stacks 0C33 "syntomic tail base-change descent"]
theorem exists_stage
    (φ : B →ₐ[G i0] C)
    (hfinitePresentation : φ.FinitePresentation)
    (hsyntomic :
      letI : Algebra (G i0) G∞ := Ring.DirectLimit.Algebra.stageAlgebra f i0
      RingHom.Syntomic (Algebra.TensorProduct.map φ (AlgHom.id (G i0) G∞)).toRingHom) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      RingHom.Syntomic
        (Algebra.TensorProduct.map φ (AlgHom.id (G i0) (G j.1))).toRingHom := sorry

end Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Syntomic
