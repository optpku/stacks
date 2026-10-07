module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.Finite

/-!
# Finitely presented module descent along direct-limit base change

This leaf contains the descent consequences controlled by finite presentation.
It builds on the arbitrary-map transport and finite-module descent leaves.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

noncomputable section

namespace Ring.DirectLimit

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I]
variable {R : I → Type w} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [IsDirectedOrder I]
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

namespace BaseChange.FinitePresentation

/-- A linear map out of the base change of a finitely presented module to the
direct limit comes from one stage. -/
@[stacks 05LI "finitely presented module base-change descent"]
theorem exists_stageMap
    {M : Type x} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    {N : Type y} [AddCommGroup N] [Module A N]
    (v : Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)) ⊗[A] M →ₗ[Ring.DirectLimit R
      (fun i j h ↦ (f i j h : R i →+* R j))]
        Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)) ⊗[A] N) :
    ∃ i : I, ∃ v_i : R i ⊗[A] M →ₗ[R i] R i ⊗[A] N,
      Ring.DirectLimit.BaseChange.stageMap f i v_i = v := sorry

/-- Bijectivity of the base change of a map from a finite module to a finitely
presented module is already witnessed at one stage of a direct limit. -/
@[stacks 05LI "finitely presented module base-change descent"]
theorem exists_bijective
    {M : Type x} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type y} [AddCommGroup N] [Module A N] [Module.FinitePresentation A N]
    (u : M →ₗ[A] N)
    (h : Function.Bijective
      (u.baseChange (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))))) :
    ∃ i : I, Function.Bijective (u.baseChange (R i)) := sorry

end BaseChange.FinitePresentation

end Ring.DirectLimit
