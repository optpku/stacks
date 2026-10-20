module

public import ReasLib.LinearAlgebra.ExteriorPower.LeftTensor
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact exterior-power sequences

This leaf owns the linear-algebraic exactness statement for the canonical
left-tensor and functorial exterior-power maps.  It is independent of any
particular presentation of a short exact sequence.
-/

@[expose] public section

namespace exteriorPower

universe u v w x

variable {R : Type u} [CommRing R]
variable {M₂ : Type v} [AddCommGroup M₂] [Module R M₂]
variable {M₁ : Type w} [AddCommGroup M₁] [Module R M₁]
variable {M : Type x} [AddCommGroup M] [Module R M]

/-- The exterior-power map induced by `g` annihilates the canonical left-tensor map induced by
`f` whenever `g.comp f = 0`. -/
@[stacks 00DO]
theorem map_comp_leftTensorMap_eq_zero (n : ℕ) {f : M₂ →ₗ[R] M₁} {g : M₁ →ₗ[R] M}
    (hfg : g.comp f = 0) :
    (map (n + 1) g).comp (leftTensorMap n f) = 0 := sorry

/-- The range of the canonical left-tensor map lies in the kernel of the induced exterior-power
map whenever the underlying composite is zero. -/
@[stacks 00DO]
theorem range_leftTensorMap_le_ker_map (n : ℕ) {f : M₂ →ₗ[R] M₁} {g : M₁ →ₗ[R] M}
    (hfg : g.comp f = 0) :
    LinearMap.range (leftTensorMap n f) ≤ LinearMap.ker (map (n + 1) g) := sorry

/-- Exactness of the canonical exterior-power sequence induced by an exact, surjective pair of
linear maps. -/
@[stacks 00DO]
theorem exact_leftTensorMap_map (n : ℕ) {f : M₂ →ₗ[R] M₁} {g : M₁ →ₗ[R] M}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (leftTensorMap n f) (map (n + 1) g) := sorry

end exteriorPower
