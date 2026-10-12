/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap61.Lemma_61_12_17_Composition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {R S T : X.carrier} (f : R ⟶ S) (g : S ⟶ T)

/- Lemma 61.12.17 (1): for composable morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z` in a chosen big pro-étale site, the associated big pro-étale
morphisms of topoi satisfy `g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 098U] #check
  (Big.morphismOfTopoi_comp.{u, v, max u v} f g :
    MorphismOfTopoiIn.comp (Big.morphismOfTopoi g) (Big.morphismOfTopoi f) =
      Big.morphismOfTopoi (f ≫ g))

/- Lemma 61.12.17 (2): for composable morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z` in a chosen big pro-étale site, the associated small pro-étale
morphisms of topoi satisfy `g_small ∘ f_small = (g ∘ f)_small`. -/
@[stacks 098U] #check
  (SmallToBig.smallMorphism_comp.{u, v, max u v} f g :
    MorphismOfTopoiIn.comp (SmallToBig.smallMorphism g)
        (SmallToBig.smallMorphism f) =
      SmallToBig.smallMorphism (f ≫ g))

end AlgebraicGeometry.ChosenBigProetaleSite
