/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Descent

/-!
# Source locality of étale scheme morphisms

This file records that étaleness of scheme morphisms is local on the source for the étale
precoverage.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Etale

/-- Étaleness of scheme morphisms is local on the source for the étale precoverage. -/
instance isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Etale :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Etale
