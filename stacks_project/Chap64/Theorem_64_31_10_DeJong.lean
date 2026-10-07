module

public import stacks_project.Chap64.Theorem_64_31_8_GeometricMonodromy

/-!
# de Jong's conjecture at a fixed prime

This leaf owns the prime-specific form of de Jong's finite geometric monodromy
conjecture used by residual `GL n (ZMod ℓ)` deformation problems. The all-prime
form remains `deJongConjecture` in `Theorem_64_31_8_GeometricMonodromy`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix
open scoped PowerSeries.WithPiTopology

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- de Jong's conjecture at a prime `ℓ` and rank `n`: every continuous representation
`ρ : etaleFundamentalGroup X.left (arithmeticPoint X xbar) →ₜ*
GL (Fin n) (PowerSeries (ZMod ℓ))` has finite geometric monodromy. -/
def deJongConjectureAt {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) (ℓ n : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ ρ : GLPowerSeriesRep X n ℓ xbar, HasFiniteGeometricMonodromy ρ

/-- Unfolding of the prime-specific de Jong conjecture as finite geometric monodromy of
every continuous `GL (Fin n) (PowerSeries (ZMod ℓ))`-valued representation. -/
theorem deJongConjectureAt_iff {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) (ℓ n : ℕ) [Fact ℓ.Prime] :
    deJongConjectureAt X xbar ℓ n ↔
      ∀ ρ : etaleFundamentalGroup X.left (arithmeticPoint X xbar) →ₜ*
          GL (Fin n) (PowerSeries (ZMod ℓ)),
        HasFiniteGeometricMonodromy ρ := sorry

end AlgebraicGeometry.SchemeOverField
