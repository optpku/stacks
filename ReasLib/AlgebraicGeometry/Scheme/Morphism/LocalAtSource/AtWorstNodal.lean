/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal

@[expose] public section

universe u

namespace AlgebraicGeometry.AtWorstNodal

/-- At-worst-nodality of relative dimension one is local on the source for the étale
precoverage. -/
instance isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.AtWorstNodal :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.AtWorstNodal
