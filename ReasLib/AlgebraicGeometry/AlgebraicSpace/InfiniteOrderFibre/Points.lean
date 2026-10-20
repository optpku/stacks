module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.GroupTheory.OrderOfElement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.Quotient

/-!
# Integer points of the affine line and the fibre `F_{x,z}`

This module records the integer sections of `𝔸¹_K`, the corresponding points of `W`, the point
`x` of `X` coming from `t = 0`, the unique point `z` of `Spec(K)`, and the identification of
the fibre with the range of those integer points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AffineSpace
open AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre

/-- The section of `𝔸¹_K` over `Spec(K)` with coordinate `t = n`. -/
def integerSection (K : Type u) [Field K] [CharZero K] (n : ℤ) :
    specK K ⟶ affineLine K :=
  homOfVector (𝟙 (specK K)) fun _ : ULift.{u} (Fin 1) ↦ (n : Γ(specK K, ⊤))

/-- The closed point of `Spec(K)` viewed as a point of the affine line via `t = n`. -/
def integerSectionPoint (K : Type u) [Field K] [CharZero K] (n : ℤ) : affineLine K :=
  integerSection K n (IsLocalRing.closedPoint K)

/-- The point of `W = 𝔸¹_K` corresponding to the integer section `t = n`. -/
def integerPoint (K : Type u) [Field K] [CharZero K] (n : ℤ) : Points (W K) :=
  ofOver.pointsEquiv (affineOver K) (integerSectionPoint K n)

/-- The unique point of `Z = Spec(K)`. -/
def z (K : Type u) [Field K] [CharZero K] : Points (Z K) :=
  ofOver.pointsEquiv (specOver K) (IsLocalRing.closedPoint K)

/-- The algebraic space `Spec(K)` has a unique point, namely `z`. -/
theorem z_unique (K : Type u) [Field K] [CharZero K] :
    ∀ w : Points (Z K), w = z K := sorry

/-- The point `x` of `X = 𝔸¹_K/ℤ` corresponding to `t = 0`. -/
def x (K : Type u) [Field K] [CharZero K] (σ : RingAut K) : Points (X K σ) :=
  Points.map (p K σ) (integerPoint K 0)

/-- Every integer point of `W` maps to `x` along `p`. -/
theorem map_p_integerPoint (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    Points.map (p K σ) (integerPoint K n) = x K σ := sorry

/-- Every integer point of `W` maps to the unique point `z` along `q`. -/
theorem map_q_integerPoint (K : Type u) [Field K] [CharZero K] (n : ℤ) :
    Points.map (q K) (integerPoint K n) = z K := sorry

/-- Every integer point of `W` lies in the fibre `F_{x, z}`. -/
theorem integerPoint_mem_fibre (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    integerPoint K n ∈ Points.fibre (p K σ) (q K) (x K σ) (z K) := sorry

/-- Distinct integers determine distinct points of `W = 𝔸¹_K`. -/
theorem integerPoint_injective (K : Type u) [Field K] [CharZero K] :
    Function.Injective (integerPoint K) := sorry

/-- For an infinite-order field automorphism, the quotient square of the affine-line
projection by the semilinear integer action is cartesian. -/
theorem isPullback (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    IsPullback (q K) (p K σ) (g K σ hσ) (f K σ hσ) := sorry

/-- The simultaneous point fibre over the origin orbit and the field-spectrum point is
exactly the range of the integer points of the affine line. -/
theorem fibre_eq_range_integerPoint (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    Points.fibre (p K σ) (q K) (x K σ) (z K) = Set.range (integerPoint K) := sorry

end AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre
