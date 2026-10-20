module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 73.4.12 (1): for composable morphisms of algebraic spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` over a scheme `S`, the associated big étale morphisms of topoi
satisfy `g_big ∘ f_big = (g ∘ f)_big`, through the canonical comparison of
their inverse-image functors. -/
@[stacks 0DF7] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi_comp_inverseImageIso :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      (MorphismOfTopoiIn.comp
        (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi g)
        (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi f)).inverseImage ≅
          (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi (f ≫ g)).inverseImage)

/- Lemma 73.4.12 (2): for composable morphisms of algebraic spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` over a scheme `S`, the associated morphisms of small étale topoi
`Sh(X_étale)` satisfy `g_small ∘ f_small = (g ∘ f)_small`, through the canonical
comparison of their inverse-image functors. -/
@[stacks 0DF7] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoiComp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi (f ≫ g)).inverseImage ≅
        ((AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi g).comp
          (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi f)).inverseImage)
