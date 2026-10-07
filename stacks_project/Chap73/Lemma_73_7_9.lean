module

import StacksCheckRecall
public import stacks_project.Chap73.Lemma_73_7_9_Composition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Fppf.Big
open scoped MorphismOfTopoiIn

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 73.7.9: for composable morphisms of algebraic spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` over a scheme `S`, the associated big fppf morphisms of topoi
satisfy `g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 0DFE] #check
  (morphismOfTopoi_comp f g :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g))
