/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Composition

/-!
Geometric composition is represented by canonical natural isomorphisms of
inverse-image functors rather than equality of the chosen adjunction data.
-/

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
  (AlgebraicGeometry.ChosenBigProetaleSite.Big.morphismOfTopoi_comp_inverseImageIso.{u, v, max u v}
    f g :
    (MorphismOfTopoiIn.comp (Big.morphismOfTopoi g) (Big.morphismOfTopoi f)).inverseImage ≅
      (Big.morphismOfTopoi (f ≫ g)).inverseImage)

/- Lemma 61.12.17 (2): for composable morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z` in a chosen big pro-étale site, the associated small pro-étale
morphisms of topoi satisfy `g_small ∘ f_small = (g ∘ f)_small`. -/
@[stacks 098U] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallMorphism_inverseImage_compIso.{u, v, max u v}
    f g :
    (MorphismOfTopoiIn.comp (SmallToBig.smallMorphism g)
        (SmallToBig.smallMorphism f)).inverseImage ≅
      (SmallToBig.smallMorphism (f ≫ g)).inverseImage)

end AlgebraicGeometry.ChosenBigProetaleSite
