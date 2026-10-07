module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap64.Definition_64_19_1_EulerFactor
public import stacks_project.Chap64.Definition_64_19_1_FrobeniusStalk

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u v

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- The actions of `ZMod p` and `k` on `κ(x)` form a scalar tower. -/
instance residueField_isScalarTower_zmod (X : SchemeOverField k) (x : X.left) :
    IsScalarTower (ZMod p) k (X.left.residueField x) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The exponent `finiteFieldRank k p` is nonzero, so `PowerSeries.expand` by this
factor is defined. -/
theorem finiteFieldRank_ne_zero (k : Type u) [Field k] [Fintype k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    finiteFieldRank k p ≠ 0 := sorry

/-- The product of the ground-field rank with the residue degree at a closed point
is the prime-field degree of `κ(x)`. -/
theorem residueDegree_mul_finiteFieldRank [Fintype k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left) :
    finiteFieldRank k p * X.hom.residueDegree x.1 =
      Module.finrank (ZMod p) (X.left.residueField x.1) := sorry

/-- Remark 64.19.2: the indeterminate `T` in an L-function Euler factor is read as
`t ^ finiteFieldRank k p`, where `p ^ finiteFieldRank k p = Fintype.card k` by
`FiniteField.pow_finrank_eq_card`. After this `PowerSeries.expand`, the local factor
`LinearMap.eulerFactor φ (X.hom.residueDegree x)` equals
`LinearMap.eulerFactor φ (Module.finrank (ZMod p) (X.left.residueField x))`,
so the definitions do not depend on the size of the finite ground field. -/
@[stacks 03UW]
theorem expand_eulerFactor_residueDegree
    {Λ : Type u} {M : Type v} [CommRing Λ] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] [Module.Projective Λ M] [Fintype k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left)
    (φ : M →ₗ[Λ] M) :
    PowerSeries.expand (finiteFieldRank k p) (finiteFieldRank_ne_zero k p)
        (LinearMap.eulerFactor φ (X.hom.residueDegree x.1)) =
      LinearMap.eulerFactor φ (Module.finrank (ZMod p) (X.left.residueField x.1)) := sorry

end AlgebraicGeometry.SchemeOverField
