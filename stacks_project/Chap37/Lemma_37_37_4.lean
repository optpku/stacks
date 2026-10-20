/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.GeometricallyUnibranch

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/- Lemma 37.37.4 (1): if `Y` is integral and geometrically unibranch, the composite
`f ≫ g` is étale, and every irreducible component of `X` dominates `Y`, then `f` is
étale. -/
@[stacks 0GSB]
#check (AlgebraicGeometry.Scheme.Hom.EtaleAt.left_of_comp_of_dominantComponents :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y]
    [Etale (f ≫ g)],
    (h_geom : Y.isGeometricallyUnibranch) →
    (h_components : ∀ C : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι C ≫ f)) →
    Etale f)

/- Lemma 37.37.4 (2): if `Y` is integral and geometrically unibranch, the composite
`f ≫ g` is étale, and every irreducible component of `X` dominates `Y`, then `g` is
étale at every point in the image of `f`. -/
@[stacks 0GSB]
#check (AlgebraicGeometry.Scheme.Hom.EtaleAt.right_of_comp_of_dominantComponents :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y]
    [Etale (f ≫ g)],
    (h_geom : Y.isGeometricallyUnibranch) →
    (h_components : ∀ C : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι C ≫ f)) →
    ∀ x : X, g.EtaleAt (f x))

end AlgebraicGeometry
