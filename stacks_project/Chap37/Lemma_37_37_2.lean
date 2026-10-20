/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.GeometricallyUnibranch
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.37.2 (1): if an unramified morphism `f : X ⟶ Y` has connected source,
integral geometrically unibranch target, and an irreducible component of `X` dominating `Y`,
then `f` is étale. -/
@[stacks 0GS9]
#check
  (AlgebraicGeometry.Scheme.Hom.etale_of_dominantComponent :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [ConnectedSpace X] [Unramified f],
      Y.isGeometricallyUnibranch →
      (∃ Z : irreducibleComponents X,
        IsDominant (X.irreducibleComponentSubschemeι Z ≫ f)) →
      Etale f)

/- Lemma 37.37.2 (2): if an unramified morphism `f : X ⟶ Y` has connected source,
integral geometrically unibranch target, and an irreducible component of `X` dominating `Y`,
then `X` is irreducible. -/
@[stacks 0GS9]
#check
  (AlgebraicGeometry.Scheme.Hom.irreducibleSpace_of_dominantComponent :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [ConnectedSpace X] [Unramified f],
      Y.isGeometricallyUnibranch →
      (∃ Z : irreducibleComponents X,
        IsDominant (X.irreducibleComponentSubschemeι Z ≫ f)) →
      IrreducibleSpace X)

end AlgebraicGeometry.Scheme.Hom
