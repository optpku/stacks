/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Sites.Over.Topos.Composition
import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u v

variable (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v})
  {S : Schh.carrier} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 38.34.19: the morphisms of topoi induced on the big h sites satisfy
`g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 0EU7] #check
  (CategoryTheory.Over.Site.morphismOfTopoi_comp.{v, u, max u v}
      Schh.toGrothendieck f.left g.left :
    MorphismOfTopoiIn.comp
        (CategoryTheory.Over.Site.morphismOfTopoi.{v, u, max u v}
          Schh.toGrothendieck g.left)
        (CategoryTheory.Over.Site.morphismOfTopoi.{v, u, max u v}
          Schh.toGrothendieck f.left) =
      CategoryTheory.Over.Site.morphismOfTopoi.{v, u, max u v}
        Schh.toGrothendieck (f.left ≫ g.left))
