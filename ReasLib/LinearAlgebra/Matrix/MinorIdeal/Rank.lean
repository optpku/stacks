module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic
public import ReasLib.LinearAlgebra.ExteriorPower.Zero

/-!
# Rank minor ideals of coordinate linear maps

This leaf packages the exterior rank of a map between standard finite free
modules and the determinantal ideal at that rank.
-/

@[expose] public section

universe u

open Matrix exteriorPower

namespace LinearMap

section

variable {R : Type u} [CommRing R] {m n : ℕ}

/-- Definition 10.102.5: the exterior rank of a coordinate linear map is the largest exterior
power on which it is nonzero. -/
@[stacks 00MV "exterior rank"]
noncomputable def exteriorRank (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : ℕ :=
  letI : DecidablePred fun r ↦ exteriorPower.map r φ ≠ 0 := Classical.decPred _
  Nat.findGreatest (fun r ↦ exteriorPower.map r φ ≠ 0) (min m n)

/-- The exterior rank of a coordinate linear map is bounded by the smaller displayed rank. -/
theorem exteriorRank_le_min (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorRank φ ≤ min m n := sorry

/-- Definition 10.102.5: the rank-minor ideal of a coordinate linear map. -/
@[stacks 00MV "rank minor ideals"]
noncomputable def rankMinorIdeal (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : Ideal R :=
  Matrix.minorIdeal (exteriorRank φ) <|
    LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ

/-! Textbook notation for the rank-minor ideal. -/
notation:max "I(" φ ")" => LinearMap.rankMinorIdeal φ

/-- Every rank-sized minor of the coordinate matrix belongs to the rank-minor ideal. -/
theorem det_submatrix_mem_rankMinorIdeal (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (e₁ : Fin (exteriorRank φ) ↪ Fin n) (e₂ : Fin (exteriorRank φ) ↪ Fin m) :
    Matrix.det
        ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix e₁ e₂) ∈
      I(φ) := sorry

/-- The zero coordinate map has exterior rank zero. -/
@[stacks 00MV "exterior rank of the zero map"]
theorem exteriorRank_zero_eq_zero {m n : ℕ} :
    exteriorRank (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = 0 := sorry

/-- The rank-minor ideal of the zero coordinate map is the unit ideal. -/
@[stacks 00MV "rank-minor ideal of the zero map"]
theorem rankMinorIdeal_zero_eq_top {m n : ℕ} :
    rankMinorIdeal (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = ⊤ := sorry

/-- Exterior rank zero is equivalent to vanishing for a coordinate linear map. -/
@[stacks 00MV "exterior rank zero criterion"]
theorem exteriorRank_eq_zero_iff_eq_zero {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorRank φ = 0 ↔ φ = 0 := sorry

end

end LinearMap
