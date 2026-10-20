module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

/-!
# Finite irreducible components of irreducible schemes

Irreducible schemes have finitely many irreducible components on every quasi-compact open.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- An irreducible scheme has finitely many irreducible components on every quasi-compact open. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensOfIrreducibleSpace
    (X : Scheme.{u}) [IrreducibleSpace X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

end AlgebraicGeometry.Scheme
