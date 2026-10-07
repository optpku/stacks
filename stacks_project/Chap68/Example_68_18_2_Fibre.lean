module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.GroupTheory.OrderOfElement
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap68.«68_18_0_2_Fibre»
public import stacks_project.Chap68.Example_68_18_2_Space

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

/-- `integerSection n` is `homOfVector` of the constant global section `n`. -/
theorem integerSection_eq (K : Type u) [Field K] [CharZero K] (n : ℤ) :
    integerSection K n =
      homOfVector (𝟙 (specK K)) fun _ : ULift.{u} (Fin 1) ↦ (n : Γ(specK K, ⊤)) :=
  sorry

/-- The closed point of `Spec(K)` viewed as a point of the affine line via `t = n`. -/
def integerSectionPoint (K : Type u) [Field K] [CharZero K] (n : ℤ) : affineLine K :=
  integerSection K n (IsLocalRing.closedPoint K)

/-- `integerSectionPoint n` is the image of the closed point under `integerSection n`. -/
theorem integerSectionPoint_eq (K : Type u) [Field K] [CharZero K] (n : ℤ) :
    integerSectionPoint K n = integerSection K n (IsLocalRing.closedPoint K) := sorry

/-- The point of `W = 𝔸¹_K` corresponding to the integer section `t = n`. -/
def integerPoint (K : Type u) [Field K] [CharZero K] (n : ℤ) : Points (W K) :=
  ofOver.pointsEquiv (affineOver K) (integerSectionPoint K n)

/-- `integerPoint n` is the image of `integerSectionPoint n` under `ofOver.pointsEquiv`. -/
theorem integerPoint_eq (K : Type u) [Field K] [CharZero K] (n : ℤ) :
    integerPoint K n = ofOver.pointsEquiv (affineOver K) (integerSectionPoint K n) := sorry

/-- The origin section `t = 0` of `𝔸¹_K`. -/
theorem integerPoint_zero (K : Type u) [Field K] [CharZero K] :
    integerPoint K 0 = ofOver.pointsEquiv (affineOver K) (integerSectionPoint K 0) := sorry

/-- The unique point of `Z = Spec(K)`. -/
def z (K : Type u) [Field K] [CharZero K] : Points (Z K) :=
  ofOver.pointsEquiv (specOver K) (IsLocalRing.closedPoint K)

/-- `z` is the image of the closed point of `Spec(K)` under `ofOver.pointsEquiv`. -/
theorem z_eq (K : Type u) [Field K] [CharZero K] :
    z K = ofOver.pointsEquiv (specOver K) (IsLocalRing.closedPoint K) := sorry

/-- The algebraic space `Spec(K)` has a unique point, namely `z`. -/
instance instUnique_points_Z (K : Type u) [Field K] [CharZero K] : Unique (Points (Z K)) where
  default := z K
  uniq := sorry

/-- The default point of `Z` is `z`. -/
theorem default_points_Z (K : Type u) [Field K] [CharZero K] :
    (default : Points (Z K)) = z K := sorry

/-- The point `x` of `X = 𝔸¹_K/ℤ` corresponding to `t = 0`. -/
def x (K : Type u) [Field K] [CharZero K] (σ : RingAut K) : Points (X K σ) :=
  Points.map (p K σ) (integerPoint K 0)

/-- `x` is the image of the origin integer point under the atlas `p`. -/
theorem x_eq (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    x K σ = Points.map (p K σ) (integerPoint K 0) := sorry

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

end AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre
