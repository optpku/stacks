/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

@[expose] public section

universe u

open scoped MatrixGroups

namespace Matrix.ProjGenLinGroup

variable {R : Type u} [CommRing R]

/-- A diagonal entry of a projective-kernel matrix times the corresponding inverse entry is one. -/
theorem kernelEntry_mul_invEntry (d : ℕ)
    (A : (mk : GL (Fin d) R →* PGL(d, R)).ker) (i : Fin d) :
    A.1 i i * A.1⁻¹ i i = 1 := by
  obtain ⟨unit, hunit⟩ : ∃ unit : Rˣ, GeneralLinearGroup.scalar (Fin d) unit = A.1 := by
    simpa only [ker_mk, GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range]
      using A.2
  rw [← hunit, ← map_inv]
  change (GeneralLinearGroup.scalar (Fin d) unit : Matrix (Fin d) (Fin d) R) i i *
    (GeneralLinearGroup.scalar (Fin d) unit⁻¹ : Matrix (Fin d) (Fin d) R) i i = 1
  simpa only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] using unit.mul_inv

/-- A diagonal entry of the inverse of a projective-kernel matrix times its original entry is one. -/
theorem invEntry_mul_kernelEntry (d : ℕ)
    (A : (mk : GL (Fin d) R →* PGL(d, R)).ker) (i : Fin d) :
    A.1⁻¹ i i * A.1 i i = 1 := by
  rw [mul_comm]
  exact kernelEntry_mul_invEntry d A i

/-- The unit represented by the first diagonal entry of a projective-kernel matrix,
with inverse supplied by the corresponding entry of the inverse matrix. -/
def kernelScalarUnit (d : ℕ) (hd : 0 < d)
    (A : (mk : GL (Fin d) R →* PGL(d, R)).ker) : Rˣ :=
  let i : Fin d := ⟨0, hd⟩
  { val := A.1 i i
    inv := A.1⁻¹ i i
    val_inv := kernelEntry_mul_invEntry d A i
    inv_val := invEntry_mul_kernelEntry d A i }

/-- The scalar-matrix embedding of units into the kernel of `GL → PGL`. -/
def scalarToKer (d : ℕ) : Rˣ → (mk : GL (Fin d) R →* PGL(d, R)).ker :=
  fun unit ↦ ⟨GeneralLinearGroup.scalar (Fin d) unit, mk_scalar unit⟩

/-- Extracting the first diagonal entry is a left inverse to the scalar-kernel embedding. -/
theorem scalarToKer_leftInverse (d : ℕ) (hd : 0 < d) :
    Function.LeftInverse (kernelScalarUnit d hd (R := R)) (scalarToKer d) := by
  intro unit
  apply Units.ext
  change (GeneralLinearGroup.scalar (Fin d) unit : Matrix (Fin d) (Fin d) R)
    ⟨0, hd⟩ ⟨0, hd⟩ = (unit : R)
  simp

/-- Extracting the first diagonal entry is a right inverse to the scalar-kernel embedding. -/
theorem scalarToKer_rightInverse (d : ℕ) (hd : 0 < d) :
    Function.RightInverse (kernelScalarUnit d hd (R := R)) (scalarToKer d) := by
  intro A
  obtain ⟨unit, hunit⟩ : ∃ unit : Rˣ, GeneralLinearGroup.scalar (Fin d) unit = A.1 := by
    simpa only [ker_mk, GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range]
      using A.2
  have hA : scalarToKer d unit = A := Subtype.ext hunit
  rw [← hA, scalarToKer_leftInverse d hd unit]

/-- The scalar-kernel embedding preserves multiplication of units. -/
theorem scalarToKer_mul (d : ℕ) (unit₁ unit₂ : Rˣ) :
    scalarToKer d (unit₁ * unit₂) = scalarToKer d unit₁ * scalarToKer d unit₂ := by
  apply Subtype.ext
  exact (GeneralLinearGroup.scalar (Fin d)).map_mul unit₁ unit₂

/-- Units are multiplicatively equivalent to the kernel of `GL → PGL` in positive dimension. -/
def scalarEquivKer (d : ℕ) (hd : 0 < d) :
    Rˣ ≃* (mk : GL (Fin d) R →* PGL(d, R)).ker where
  toFun := scalarToKer d
  invFun := kernelScalarUnit d hd
  left_inv := scalarToKer_leftInverse d hd
  right_inv := scalarToKer_rightInverse d hd
  map_mul' := scalarToKer_mul d

/-- The forward map of the scalar-kernel equivalence is the scalar matrix embedding. -/
theorem scalarEquivKer_apply (d : ℕ) (hd : 0 < d) (unit : Rˣ) :
    (scalarEquivKer d hd unit).1 = GeneralLinearGroup.scalar (Fin d) unit := rfl

/-- Every projective-kernel matrix is recovered from its scalar representative. -/
theorem scalarEquivKer_symm_spec (d : ℕ) (hd : 0 < d)
    (A : (mk : GL (Fin d) R →* PGL(d, R)).ker) :
    scalarToKer d ((scalarEquivKer d hd).symm A) = A :=
  (scalarEquivKer d hd).apply_symm_apply A

end Matrix.ProjGenLinGroup

end
