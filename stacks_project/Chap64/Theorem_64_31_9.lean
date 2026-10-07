module

public import stacks_project.Chap64.Theorem_64_31_10_DeJong
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open scoped PowerSeries.WithPiTopology

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Theorem 64.31.9. Let `k` be a finite field and let `X` be a geometrically irreducible
smooth projective curve over `k`. If `2 * n < ℓ`, then de Jong's conjecture holds at the
prime `ℓ` and rank `n`: every continuous `ρ : etaleFundamentalGroup X.left
(arithmeticPoint X xbar) →ₜ* GL (Fin n) (PowerSeries (ZMod ℓ))` has finite geometric
monodromy. The source records this as Gaitsgory's theorem modulo some unproven things. -/
@[stacks 03W0]
theorem deJongConjectureAt_of_prime_gt_two_mul
    {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : 2 * n < ℓ) :
    deJongConjectureAt X xbar ℓ n := sorry

/-- Apply-form of the `2 * n < ℓ` case: a continuous `GL (Fin n)` power series representation
has finite geometric monodromy. -/
theorem hasFiniteGeometricMonodromy_of_prime_gt_two_mul
    {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : 2 * n < ℓ) (ρ : GLPowerSeriesRep X n ℓ xbar) :
    HasFiniteGeometricMonodromy ρ := sorry

end AlgebraicGeometry.SchemeOverField
