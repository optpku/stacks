/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Locality

@[expose] public section

universe u

namespace AlgebraicGeometry.Unramified

/- Unramifiedness of scheme morphisms is local on the source for the étale precoverage. -/
#check (isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Unramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)

end AlgebraicGeometry.Unramified

namespace AlgebraicGeometry.GUnramified

/- G-unramifiedness of scheme morphisms is local on the source for the étale precoverage. -/
#check (isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.GUnramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)

end AlgebraicGeometry.GUnramified
