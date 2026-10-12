/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap73.Lemma_73_4_12_Composition
public import stacks_project.Chap66.Lemma_66_18_8_Topos

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.Big
open scoped MorphismOfTopoiIn

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 73.4.12 (1): for composable morphisms of algebraic spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` over a scheme `S`, the associated big étale morphisms of topoi
satisfy `g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 0DF7] #check
  (morphismOfTopoi_comp f g :
    MorphismOfTopoiIn.comp (Etale.Big.morphismOfTopoi g) (Etale.Big.morphismOfTopoi f) =
      Etale.Big.morphismOfTopoi (f ≫ g))

/- Lemma 73.4.12 (2): for composable morphisms of algebraic spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` over a scheme `S`, the associated morphisms of small étale topoi
`Sh(X_étale)` satisfy `g_small ∘ f_small = (g ∘ f)_small`. -/
@[stacks 0DF7] #check
  (smallEtaleMorphismOfTopoiComp f g :
    (smallEtaleMorphismOfTopoi (f ≫ g)).inverseImage ≅
      ((smallEtaleMorphismOfTopoi g).comp (smallEtaleMorphismOfTopoi f)).inverseImage)
