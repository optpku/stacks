module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.TensorProduct.Domination
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import ReasLib.LinearAlgebra.Quotient.Descent

/-!
# Tensor-kernel domination and surjections

Tensor-kernel domination is invariant under precomposition by a surjective linear map. This is
the descent interface used when a source is replaced by a free presentation.
-/

@[expose] public section

universe u v w x

namespace LinearMap.Dominates

section Semiring

variable {R : Type u} [CommSemiring R]
variable {A A' B C : Type v}
variable [AddCommMonoid A] [Module R A]
variable [AddCommMonoid A'] [Module R A']
variable [AddCommMonoid B] [Module R B]
variable [AddCommMonoid C] [Module R C]

/-- Precomposition by a surjective linear map preserves and reflects tensor-kernel
domination. -/
@[stacks 059B "surjective precomposition"]
theorem comp_iff_of_surjective {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (q : A' →ₗ[R] A) (hq : Function.Surjective q) :
    (g.comp q).Dominates (f.comp q) ↔ g.Dominates f := by
  constructor
  · intro hdom Q _ _ x hx
    obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective Q hq x
    rw [LinearMap.mem_ker] at hx ⊢
    have hy : y ∈ LinearMap.ker ((f.comp q).rTensor Q) := by
      rw [LinearMap.mem_ker, LinearMap.rTensor_comp_apply]
      exact hx
    have hyg := LinearMap.mem_ker.mp (hdom Q hy)
    simpa only [LinearMap.rTensor_comp_apply] using hyg
  · exact fun hdom ↦ hdom.comp

end Semiring

section Ring

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {C : Type x}
variable [AddCommGroup A] [Module R A]
variable [AddCommGroup B] [Module R B]
variable [AddCommGroup C] [Module R C]

/-- A map that tensor-kernel dominates a surjection factors through that surjection. -/
@[stacks 059B "surjective factorization"]
theorem factorsThrough_of_surjective (q : A →ₗ[R] B) (g : A →ₗ[R] C)
    (hq : Function.Surjective q) (hdom : g.Dominates q) :
    ∃ g' : B →ₗ[R] C, g = g'.comp q := by
  let g' := LinearMap.descendOfSurjective q hq g hdom.ker_le
  refine ⟨g', ?_⟩
  exact (LinearMap.descendOfSurjective_comp q hq g hdom.ker_le).symm

end Ring

end LinearMap.Dominates
