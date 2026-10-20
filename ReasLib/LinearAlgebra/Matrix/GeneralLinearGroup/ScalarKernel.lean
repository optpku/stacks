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
    A.1 i i * A.1⁻¹ i i = 1 := sorry

/-- A diagonal entry of the inverse of a projective-kernel matrix times its original entry is one. -/
theorem invEntry_mul_kernelEntry (d : ℕ)
    (A : (mk : GL (Fin d) R →* PGL(d, R)).ker) (i : Fin d) :
    A.1⁻¹ i i * A.1 i i = 1 := sorry

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
    Function.LeftInverse (kernelScalarUnit d hd (R := R)) (scalarToKer d) := sorry

/-- Extracting the first diagonal entry is a right inverse to the scalar-kernel embedding. -/
theorem scalarToKer_rightInverse (d : ℕ) (hd : 0 < d) :
    Function.RightInverse (kernelScalarUnit d hd (R := R)) (scalarToKer d) := sorry

/-- The scalar-kernel embedding preserves multiplication of units. -/
theorem scalarToKer_mul (d : ℕ) (unit₁ unit₂ : Rˣ) :
    scalarToKer d (unit₁ * unit₂) = scalarToKer d unit₁ * scalarToKer d unit₂ := sorry

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
    (scalarEquivKer d hd unit).1 = GeneralLinearGroup.scalar (Fin d) unit := sorry

/-- Every projective-kernel matrix is recovered from its scalar representative. -/
theorem scalarEquivKer_symm_spec (d : ℕ) (hd : 0 < d)
    (A : (mk : GL (Fin d) R →* PGL(d, R)).ker) :
    scalarToKer d ((scalarEquivKer d hd).symm A) = A := sorry

end Matrix.ProjGenLinGroup

end
