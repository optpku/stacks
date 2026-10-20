/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.RingTheory.Discriminant

@[expose] public section

universe u v w

open Module

namespace FieldExtension

variable (K : Type u) [Field K]

/-- Field elements, including zero, modulo multiplication by a square of a unit. -/
def SquareClassWithZero := MulAction.orbitRel.Quotient (Subgroup.square Kˣ) K

namespace SquareClassWithZero

/-- The square class with zero represented by a field element. -/
def mk (a : K) : SquareClassWithZero K := Quotient.mk'' a

/-- The zero square class with zero. -/
def zero : SquareClassWithZero K := mk K 0

/-- The unit square class with zero. -/
def one : SquareClassWithZero K := mk K 1

/-- Two field elements represent the same square class exactly when their ratio is a unit square. -/
theorem mk_eq_mk_iff {a b : K} :
    mk K a = mk K b ↔ ∃ u : Kˣ, a = (u ^ (2 : ℕ)) * b :=
    by
  change (Quotient.mk'' a : Quotient (MulAction.orbitRel (Subgroup.square Kˣ) K)) =
      Quotient.mk'' b ↔ _
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, hu⟩
    rcases (Subgroup.mem_square.mp u.2) with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    calc
      a = u • b := hu.symm
      _ = ((u : Subgroup.square Kˣ) : Kˣ) • b := by rw [MulAction.subgroup_smul_def]
      _ = (((u : Subgroup.square Kˣ) : Kˣ) : K) * b := by simp [Units.smul_def]
      _ = ↑(v ^ (2 : ℕ)) * b := by rw [hv, pow_two]
  · rintro ⟨u, hu⟩
    refine ⟨⟨u ^ (2 : ℕ), Subgroup.mem_square.mpr ⟨u, by simp [pow_two]⟩⟩, ?_⟩
    simpa [MulAction.subgroup_smul_def, Units.smul_def] using hu.symm

/-- A representative belongs to the zero class exactly when it is zero. -/
@[simp]
theorem mk_eq_zero_iff {a : K} : mk K a = zero K ↔ a = 0 := by
  simpa [zero] using (mk_eq_mk_iff (K := K) (a := a) (b := (0 : K)))

/-- A representative is outside the zero class exactly when it is nonzero. -/
@[simp]
theorem mk_ne_zero_iff {a : K} : mk K a ≠ zero K ↔ a ≠ 0 := by
  simpa only [ne_eq, mk_eq_zero_iff]

/-- A representative belongs to the unit class exactly when it is a square of a unit. -/
theorem mk_eq_one_iff {a : K} :
    mk K a = one K ↔ ∃ u : Kˣ, a = (u ^ (2 : ℕ) : K) := by
  simpa [one] using (mk_eq_mk_iff (K := K) (a := a) (b := (1 : K)))

end SquareClassWithZero

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The square class of a basis discriminant is independent of the chosen basis. -/
private theorem squareClassWithZero_eq_of_basis_discr {ι : Type w} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (b : Basis ι K L) (b' : Basis ι' K L) :
    SquareClassWithZero.mk K (Algebra.discr K b) =
      SquareClassWithZero.mk K (Algebra.discr K b') := by
  let e : ι ≃ ι' := b.indexEquiv b'
  let b₀ : Basis ι K L := b'.reindex e.symm
  have hdet : IsUnit (b₀.toMatrix b).det := by
    -- Local instance justification (proof-local temporary data): this particular change-of-basis matrix supplies the invertibility hypothesis for its determinant.
    letI := Basis.invertibleToMatrix b₀ b
    exact Matrix.isUnit_det_of_invertible (b₀.toMatrix b)
  rw [SquareClassWithZero.mk_eq_mk_iff]
  refine ⟨hdet.unit, ?_⟩
  calc
    Algebra.discr K b = (b₀.toMatrix b).det ^ 2 * Algebra.discr K b₀ := by
      calc
        Algebra.discr K b =
            Algebra.discr K (Matrix.vecMul b₀ ((b₀.toMatrix b).map (algebraMap K L))) := by
              rw [b₀.toMatrix_map_vecMul b]
        _ = (b₀.toMatrix b).det ^ 2 * Algebra.discr K b₀ := by
              simpa using Algebra.discr_of_matrix_vecMul b₀ (b₀.toMatrix b)
    _ = ↑(hdet.unit ^ (2 : ℕ)) * Algebra.discr K b₀ := by simp
    _ = ↑(hdet.unit ^ (2 : ℕ)) * Algebra.discr K b' := by
      congr 1
      simpa [b₀, Basis.coe_reindex] using
        (@Algebra.discr_reindex K L ι' _ _ _ _ ι _ _ _ b' e.symm)

section FiniteDimensional

variable [FiniteDimensional K L]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The discriminant of a finite field extension, viewed in the square classes with zero of its
base field. -/
noncomputable def discriminant (K : Type u) [Field K] (L : Type v) [Field L]
    [Algebra K L] [FiniteDimensional K L] : SquareClassWithZero K :=
  SquareClassWithZero.mk K (Algebra.discr K (Module.finBasis K L))

/-- Every basis computes the discriminant square class of a finite field extension. -/
theorem discriminant_eq (b : Basis ι K L) :
    discriminant K L = SquareClassWithZero.mk K (Algebra.discr K b) := by
  simpa [discriminant] using squareClassWithZero_eq_of_basis_discr (Module.finBasis K L) b

end FiniteDimensional

end FieldExtension
