/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.31.3 (1): unramifiedness of scheme morphisms is local on the source
for the étale precoverage. -/
@[stacks 03YV] #check
  (AlgebraicGeometry.Unramified.isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Unramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)

/- Lemma 35.31.3 (2): G-unramifiedness of scheme morphisms is local on the source
for the étale precoverage. -/
@[stacks 03YV] #check
  (AlgebraicGeometry.GUnramified.isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.GUnramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)
