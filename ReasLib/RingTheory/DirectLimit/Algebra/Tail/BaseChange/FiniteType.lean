module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FiniteType
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-type base change over a cofinal tail

The fixed-base direct-limit API is the core owner.  This leaf is its
source-facing tail adapter: a selected initial stage supplies the base ring,
and later stages are represented canonically by `Set.Ici i0`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail.BaseChange.FiniteType

variable {I : Type u} [Preorder I] [IsDirectedOrder I]
variable (G : I → Type v) [∀ i, CommRing (G i)]
variable (f : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G (fun i j h ↦ f i j h)]
variable (i0 : I)
variable {B C : Type w} [CommRing B] [CommRing C]
variable [Algebra (G i0) B] [Algebra (G i0) C]

local notation "G∞" => Ring.DirectLimit G (fun i j h ↦ f i j h)

/-- Stacks tag `07RG`: after choosing a base stage, finiteness of a
finite-type base change to the full direct limit is witnessed on its cofinal
tail.  The displayed local algebra actions are the canonical, necessarily
stage-selected actions from `Tail.stageAlgebra`. -/
@[stacks 07RG "finite-type tail base-change descent"]
theorem exists_finite
    (φ : B →ₐ[G i0] C)
    (hfinite :
      letI : Algebra (G i0) G∞ := Ring.DirectLimit.Algebra.stageAlgebra f i0
      (Algebra.TensorProduct.map φ (AlgHom.id (G i0) G∞)).Finite)
    (hfiniteType : φ.FiniteType) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      (Algebra.TensorProduct.map φ (AlgHom.id (G i0) (G j.1))).Finite := sorry

/-- Stacks tag `07RH`: after choosing a base stage, surjectivity of a
finite-type base change to the full direct limit is witnessed on its cofinal
tail.  The displayed local algebra actions are the canonical, necessarily
stage-selected actions from `Tail.stageAlgebra`. -/
@[stacks 07RH "finite-type tail base-change descent"]
theorem exists_surjective
    (φ : B →ₐ[G i0] C)
    (hsurjective :
      letI : Algebra (G i0) G∞ := Ring.DirectLimit.Algebra.stageAlgebra f i0
      Function.Surjective (Algebra.TensorProduct.map φ (AlgHom.id (G i0) G∞)))
    (hfiniteType : φ.FiniteType) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      Function.Surjective (Algebra.TensorProduct.map φ (AlgHom.id (G i0) (G j.1))) := sorry

end Ring.DirectLimit.Algebra.Tail.BaseChange.FiniteType
