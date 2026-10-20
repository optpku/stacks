/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Classifying

/-- For a flat locally finitely presented group algebraic space, the canonical
comparison from fppf torsors to principal homogeneous spaces is an equivalence. -/
instance toPrincipal_isEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    CategoryTheory.BasedFunctor.IsEquivalence
      (GroupAlgebraicSpace.toPrincipalBasedFunctor G) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Classifying
