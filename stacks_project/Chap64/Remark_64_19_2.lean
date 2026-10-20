module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.EulerFactor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u v

noncomputable section

/- Remark 64.19.2: the indeterminate `T` in an L-function Euler factor is read as
`t ^ finiteFieldRank k p`, where `p ^ finiteFieldRank k p = Fintype.card k` by
`FiniteField.pow_finrank_eq_card`. After this `PowerSeries.expand`, the local factor
`LinearMap.eulerFactor φ (X.hom.residueDegree x)` equals
`LinearMap.eulerFactor φ (Module.finrank (ZMod p) (X.left.residueField x))`,
so the definitions do not depend on the size of the finite ground field. -/
@[stacks 03UW]
#check (AlgebraicGeometry.SchemeOverField.expand_eulerFactor_residueDegree :
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    {Λ : Type u} {M : Type v} [CommRing Λ] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] [Module.Projective Λ M] [Fintype k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left)
    (φ : M →ₗ[Λ] M),
    PowerSeries.expand (finiteFieldRank k p) (Module.finrank_pos (R := ZMod p) (M := k)).ne'
        (LinearMap.eulerFactor φ (X.hom.residueDegree x.1)) =
      LinearMap.eulerFactor φ (Module.finrank (ZMod p) (X.left.residueField x.1)))
