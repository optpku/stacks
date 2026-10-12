/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap73.Lemma_73_8_9_Composition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Ph.Big
open scoped MorphismOfTopoiIn

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 73.8.9: for composable morphisms of algebraic spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` over a scheme `S`, the associated big ph morphisms of topoi
satisfy `g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 0DFP] #check
  (morphismOfTopoi_comp f g :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g))
