module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.DeJong

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix
open scoped PowerSeries.WithPiTopology

universe u

namespace AlgebraicGeometry.SchemeOverField

/- de Jong's conjecture at a fixed prime. -/
#check (AlgebraicGeometry.SchemeOverField.deJongConjectureAt :
  ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) (ℓ n : ℕ) [Fact ℓ.Prime], Prop)

/- Unfolding of the fixed-prime conjecture. -/
#check (AlgebraicGeometry.SchemeOverField.deJongConjectureAt_iff :
  ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) (ℓ n : ℕ) [Fact ℓ.Prime],
    deJongConjectureAt X xbar ℓ n ↔
      ∀ ρ : etaleFundamentalGroup X.left (arithmeticPoint X xbar) →ₜ*
          GL (Fin n) (PowerSeries (ZMod ℓ)),
        HasFiniteGeometricMonodromy ρ)

end AlgebraicGeometry.SchemeOverField
