module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

/-!
# Finite irreducible components of scheme reductions

The property that quasi-compact opens have finitely many irreducible components
is preserved by passing to the reduction of a scheme.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The reduction of a scheme with finitely many irreducible components on
quasi-compact opens has the same finiteness property. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensReduction
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X.reduction := sorry

end AlgebraicGeometry.Scheme
