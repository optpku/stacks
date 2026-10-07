module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

@[expose] public section

universe u v

namespace LinearMap

/-- For adjoint maps between finite free integral modules with symmetric positive-definite
forms and a perfect form on the source, the torsion in the cokernel of the composite is
additively equivalent to the dual of the range modulo the restricted form range. -/
theorem torsionCokerAdjointCompEquiv
    (L₀ : Type u) [AddCommGroup L₀] [Module.Finite ℤ L₀] [Module.Free ℤ L₀]
    (L₁ : Type v) [AddCommGroup L₁] [Module.Finite ℤ L₁] [Module.Free ℤ L₁]
    (B₀ : LinearMap.BilinForm ℤ L₀) (B₁ : LinearMap.BilinForm ℤ L₁)
    [IsPerfPair B₀]
    (h₀_symm : B₀.IsSymm) (h₀_pos : ∀ x : L₀, x ≠ 0 → 0 < B₀ x x)
    (h₁_symm : B₁.IsSymm) (h₁_pos : ∀ x : L₁, x ≠ 0 → 0 < B₁ x x)
    (d : L₀ →ₗ[ℤ] L₁) (dStar : L₁ →ₗ[ℤ] L₀)
    (h_adjoint : IsAdjointPair B₀ B₁ d dStar) :
    Nonempty
      (AddCommGroup.torsion (L₀ ⧸ (dStar.comp d).range) ≃+
        Module.Dual ℤ d.range ⧸ (B₁.flip.restrict d.range).range) := sorry

end LinearMap
