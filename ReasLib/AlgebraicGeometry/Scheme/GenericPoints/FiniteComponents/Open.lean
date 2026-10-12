/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

/-!
# Finite irreducible components on open subschemes

The property that quasi-compact opens have finitely many irreducible components is preserved by
restriction to an open subscheme.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Every open subscheme of a scheme with finite irreducible components on quasi-compact opens
has the same finiteness property. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensToScheme
    {X : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens X] (U : X.Opens) :
    HasFiniteIrreducibleComponentsOnCompactOpens U.toScheme := sorry

end AlgebraicGeometry.Scheme
