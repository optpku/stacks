module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic

/-!
# Hyperelliptic curves

A proper curve is hyperelliptic when it admits a linear series of degree `2` and
dimension `1`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/- A proper curve is hyperelliptic when it admits a linear series of degree `2` and
dimension `1`. -/
#check (AlgebraicGeometry.Curve.IsHyperelliptic :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom], Prop)

/- Hyperellipticity is equivalent to the existence of an invertible module of degree `2`
whose space of global sections has dimension at least `2`. -/
#check (AlgebraicGeometry.Curve.isHyperelliptic_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom],
    IsHyperelliptic X ↔
      ∃ (L : X.left.Modules) (hL : Scheme.Modules.Invertible L),
        @Scheme.Modules.curveDegreeOfInvertible k _ X.left X.hom _
            topologicalKrullDim_eq_one.le L hL = (2 : ℤ) ∧
          2 ≤ Scheme.Hom.cohomologyFinrank X.hom L 0)

end AlgebraicGeometry.Curve
