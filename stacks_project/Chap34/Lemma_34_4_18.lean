/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig

open CategoryTheory

universe u

/- Lemma 34.4.18 (1): for composable morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z`, the associated big étale morphisms of topoi satisfy
`g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 021J] #check
  (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      CategoryTheory.MorphismOfTopoiIn.comp
          (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi g)
          (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi f) =
        AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi (f ≫ g))

/- Lemma 34.4.18 (2): for composable morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z`, the associated small étale morphisms of topoi satisfy
`g_small ∘ f_small = (g ∘ f)_small`. -/
@[stacks 021J] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      CategoryTheory.MorphismOfTopoiIn.comp
          (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism g)
          (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism f) =
        AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism (f ≫ g))
