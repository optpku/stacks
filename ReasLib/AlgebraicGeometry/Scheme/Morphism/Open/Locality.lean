/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Openness of the underlying map of a scheme morphism is local on the source for the
fppf precoverage. -/
instance isOpenMap_isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (AlgebraicGeometry.topologically (@IsOpenMap) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry
