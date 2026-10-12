/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent

/-!
# Locality of local finite presentation for scheme morphisms

This file records locality properties of locally finitely presented morphisms of schemes.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.LocallyOfFinitePresentation

/-- Local finite presentation of scheme morphisms is local on the source for the fppf
precoverage. -/
instance isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfFinitePresentation :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.LocallyOfFinitePresentation
