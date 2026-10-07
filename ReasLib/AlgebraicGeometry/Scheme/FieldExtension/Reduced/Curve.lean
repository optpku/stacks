module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FieldExtension.Reduced

/-- The reduced base change of a geometrically irreducible curve is a curve. -/
instance instCurveBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom] :
    Curve (baseChange k K X) := sorry

end AlgebraicGeometry.FieldExtension.Reduced
