/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.OverField.TensorPower.Coordinates
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Coincidence divisors

The product of partial diagonal ideals cuts out the locus where the first
coordinate agrees with at least one later coordinate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The `i`-th partial diagonal on `tensorPower X (r + 1)`, cut out by `x = x_{i+1}`. -/
noncomputable def partialDiagonal (X : SchemeOverField k) (r : ℕ) (i : Fin r) :
    (tensorPower X (r + 1)).left.IdealSheafData :=
  (pullback.diagonal X.hom).ker.comap (pairCoord X r i).left

/-- The partial diagonal is the inverse image of the diagonal ideal. -/
theorem partialDiagonal_eq (X : SchemeOverField k) (r : ℕ) (i : Fin r) :
    partialDiagonal X r i =
      (pullback.diagonal X.hom).ker.comap (pairCoord X r i).left :=
  sorry

/-- The coincidence divisor on `tensorPower X (r + 1)` is the product of the partial diagonals. -/
noncomputable def coincidenceDivisor (X : SchemeOverField k) (r : ℕ) :
    (tensorPower X (r + 1)).left.IdealSheafData :=
  (Finset.univ : Finset (Fin r)).prod (partialDiagonal X r)

/-- The coincidence divisor is the product of the partial diagonal ideals. -/
theorem coincidenceDivisor_eq (X : SchemeOverField k) (r : ℕ) :
    coincidenceDivisor X r =
      (Finset.univ : Finset (Fin r)).prod (partialDiagonal X r) :=
  sorry

/-- The support of the coincidence divisor is the union of the partial-diagonal supports. -/
theorem support_coincidenceDivisor (X : SchemeOverField k) (r : ℕ) :
    (coincidenceDivisor X r).support =
      (Finset.univ : Finset (Fin r)).sup fun i ↦ (partialDiagonal X r i).support :=
  sorry

/-- In degree one, the coincidence divisor is the inverse image of the diagonal along the
canonical pair of coordinates `tensorPower X 2 ⟶ X ⊗ X`. -/
theorem coincidenceDivisor_one (X : SchemeOverField k) :
    coincidenceDivisor X 1 =
      (pullback.diagonal X.hom).ker.comap (pairCoord X 1 0).left :=
  sorry

/-- A closed point of `tensorPower X (r + 1)` lies on the coincidence divisor if and only if
the first coordinate equals some later coordinate. -/
theorem mem_support_coincidenceDivisor_closedPoints_iff
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] (r : ℕ)
    {z : (tensorPower X (r + 1)).left}
    (hz : z ∈ closedPoints (tensorPower X (r + 1)).left) :
    z ∈ (coincidenceDivisor X r).support ↔
      ∃ i : Fin r,
        (coord X (r + 1) 0).left.base z = (coord X (r + 1) i.succ).left.base z :=
  sorry

/-- The diagonal of a smooth curve over an algebraically closed field is an effective
Cartier divisor. -/
instance instIsEffectiveCartierDivisor_diagonal
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] :
    IsEffectiveCartierDivisor (pullback.diagonal X.hom) :=
  sorry

/-- Each partial diagonal of a smooth curve over an algebraically closed field is an
effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_partialDiagonal
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] (r : ℕ) (i : Fin r) :
    IsEffectiveCartierDivisor (partialDiagonal X r i).subschemeι :=
  sorry

/-- The coincidence divisor on every tensor power of a smooth curve over an algebraically
closed field is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_coincidenceDivisor
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] (r : ℕ) :
    IsEffectiveCartierDivisor (coincidenceDivisor X r).subschemeι :=
  sorry

/-- For a positive tensor-power degree, the coincidence locus of a smooth curve over an
algebraically closed field defines an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_coincidenceDivisor
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] (r : ℕ) (hr : 1 ≤ r) :
    IsEffectiveCartierDivisor (coincidenceDivisor X r).subschemeι :=
  sorry

/-- The ideal sheaf of the coincidence divisor is invertible. -/
theorem coincidenceDivisor_invertibleIdealSheaf
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] (r : ℕ) :
    Scheme.Modules.Invertible
      (RingedSpace.Hom.idealSheaf (coincidenceDivisor X r).subschemeι.toShHom) :=
  sorry

end AlgebraicGeometry.SchemeOverField
