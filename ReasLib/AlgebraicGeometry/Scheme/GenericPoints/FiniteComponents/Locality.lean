/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.ObjectProperty.AffineDescent

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens

/-- The property that every quasi-compact open subscheme has finitely many irreducible
components is local for the fppf precoverage. -/
instance isLocalFppf :
    CategoryTheory.ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ HasFiniteIrreducibleComponentsOnCompactOpens X)
      Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens
