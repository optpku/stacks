module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Composition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 73.7.9: for composable morphisms of algebraic spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` over a scheme `S`, the associated big fppf morphisms of topoi
satisfy `g_big ∘ f_big = (g ∘ f)_big`. This geometric composition identity
is represented by the canonical isomorphism of inverse-image functors. -/
@[stacks 0DFE] #check
  (AlgebraicGeometry.AlgebraicSpace.Fppf.Big.morphismOfTopoi_comp_inverseImageIso f g :
    (MorphismOfTopoiIn.comp
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (fppfTopology S) g)
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (fppfTopology S) f)).inverseImage ≅
        (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1}
          (fppfTopology S) (f ≫ g)).inverseImage)
