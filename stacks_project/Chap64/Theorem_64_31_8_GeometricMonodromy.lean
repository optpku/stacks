/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.OverField
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.DeJong

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open Matrix
open scoped PowerSeries.WithPiTopology

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Continuous power-series representations of the arithmetic fundamental group. -/
#check (AlgebraicGeometry.SchemeOverField.GLPowerSeriesRep :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)],
    ℕ → ℕ → GeometricPoint (geometricBaseChange X) → Type (u + 1))

/- Finite geometric monodromy of a continuous representation. -/
#check (AlgebraicGeometry.SchemeOverField.HasFiniteGeometricMonodromy :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)] {n ℓ : ℕ}
    {xbar : GeometricPoint (geometricBaseChange X)}, GLPowerSeriesRep X n ℓ xbar → Prop)

/- Subgroup-image characterization of finite geometric monodromy. -/
#check (AlgebraicGeometry.SchemeOverField.hasFiniteGeometricMonodromy_iff :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)] {n ℓ : ℕ}
    {xbar : GeometricPoint (geometricBaseChange X)} (ρ : GLPowerSeriesRep X n ℓ xbar),
    HasFiniteGeometricMonodromy ρ ↔
      Finite (MonoidHom.range (ρ.comp (geometricToArithmetic X xbar).hom).toMonoidHom))

/- De Jong's conjecture for a smooth projective geometrically irreducible curve. -/
#check (AlgebraicGeometry.SchemeOverField.deJongConjecture :
  ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)], ℕ → Prop)

/- Quantified characterization of de Jong's conjecture. -/
#check (AlgebraicGeometry.SchemeOverField.deJongConjecture_iff :
  ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)] (n : ℕ),
    deJongConjecture X n ↔
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (xbar : GeometricPoint (geometricBaseChange X))
        (ρ : GLPowerSeriesRep X n ℓ xbar), HasFiniteGeometricMonodromy ρ)

end AlgebraicGeometry.SchemeOverField
