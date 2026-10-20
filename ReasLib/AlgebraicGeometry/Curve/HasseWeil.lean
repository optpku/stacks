module

public import Mathlib.Data.Fintype.Card
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FinitePoints
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a smooth projective geometrically irreducible curve over a finite field of
cardinality `q`, the number of points over a degree-`n` extension satisfies
`|#X(L) - q^n - 1| ^ 2 ≤ 4 * g^2 * q^n`, where `g` is the genus. -/
@[stacks 0ELH]
theorem riemannHypothesis_curve
    {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (n : ℕ) (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
    (hdeg : Module.finrank k L = n) :
    |(Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ X) : ℤ) -
        (Fintype.card k : ℤ) ^ n - 1| ^ 2 ≤
      4 * (Curve.genus X : ℤ) ^ 2 * (Fintype.card k : ℤ) ^ n := sorry

end AlgebraicGeometry.SchemeOverField
