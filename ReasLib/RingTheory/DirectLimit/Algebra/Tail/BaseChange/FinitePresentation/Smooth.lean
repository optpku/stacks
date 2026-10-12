/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.Smooth
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness over a cofinal tail

This is the source-facing tail adapter for smoothness descent.  The canonical
fixed-base API remains in `DirectLimit.Algebra.BaseChange.FinitePresentation.Smooth`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Smooth

variable {I : Type u} [Preorder I] [IsDirectedOrder I]
variable (G : I → Type v) [∀ i, CommRing (G i)]
variable (f : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G (fun i j h ↦ f i j h)]
variable (i0 : I)
variable {B C : Type w} [CommRing B] [CommRing C]
variable [Algebra (G i0) B] [Algebra (G i0) C]

local notation "G∞" => Ring.DirectLimit G (fun i j h ↦ f i j h)

/-- Stacks tag `0C0B`: smoothness of the base change of a finitely presented
map to the full direct limit is witnessed on a cofinal tail. -/
@[stacks 0C0B "smooth tail base-change descent"]
theorem exists_stage
    (φ : B →ₐ[G i0] C)
    (hfinitePresentation : φ.FinitePresentation)
    (hsmooth :
      letI : Algebra (G i0) G∞ := Ring.DirectLimit.Algebra.stageAlgebra f i0
      (Algebra.TensorProduct.map φ (AlgHom.id (G i0) G∞)).Smooth) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      (Algebra.TensorProduct.map φ (AlgHom.id (G i0) (G j.1))).Smooth := sorry

end Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Smooth
