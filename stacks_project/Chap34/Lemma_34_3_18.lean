/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig

open CategoryTheory

universe u

/- Lemma 34.3.18 (1): for composable morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z`, the associated big Zariski morphisms of topoi satisfy
`g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 0212] #check
  (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      CategoryTheory.MorphismOfTopoiIn.comp
          (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi g)
          (AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi f) =
        AlgebraicGeometry.Scheme.Zariski.Big.morphismOfTopoi (f ≫ g))

/- Lemma 34.3.18 (2): for composable morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z`, the associated small Zariski morphisms of topoi satisfy
`g_small ∘ f_small = (g ∘ f)_small`. -/
@[stacks 0212] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      CategoryTheory.MorphismOfTopoiIn.comp
          (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism g)
          (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism f) =
        AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism (f ≫ g))
