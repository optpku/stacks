module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Over.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.MixedBaseChange

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
variable {X X' Y Y' : AlgebraicSpace S}
variable (f : Y ⟶ X) (g : X' ⟶ X) (f' : Y' ⟶ X') (g' : Y' ⟶ Y)
variable (sq : IsPullback g' f' f g)

/- Lemma 73.4.13 (1): for a cartesian square of algebraic spaces over `S` in
`(Spaces/S)_étale`, pulling the big étale direct image `f_big,*` back along the
relocalization morphism `i_g` agrees with first pulling back along `i_{g'}`
and then applying the spaces-étale direct image `f'_small,*`. -/
@[stacks 0DF8] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.pushforwardBaseChange_isomorphic
      f g f' g' sq :
    IsIsomorphic
      ((Etale.Big.morphismOfTopoi f) _* ⋙
        (Etale.SpacesToBig.morphismOfTopoi g)⁻¹)
      ((Etale.SpacesToBig.morphismOfTopoi g')⁻¹ ⋙
        (spacesEtaleMorphismOfTopoi f') _*))

/- Lemma 73.4.13 (2): for a cartesian square of algebraic spaces over `S` in
`(Spaces/S)_étale`, pulling the big étale direct image `f_big,*` back along
`g_big` agrees with first pulling back along `g'_big` and then applying the
big étale direct image `f'_big,*`. -/
@[stacks 0DF8] #check
  (CategoryTheory.GrothendieckTopology.Over.BaseChange.map_isIso.{u + 1, u + 1, u + 1}
      etaleTopology g' f' f g sq :
    IsIso
      (CategoryTheory.GrothendieckTopology.Over.BaseChange.map.{u + 1, u + 1, u + 1}
        etaleTopology g' f' f g sq.w))

end AlgebraicGeometry.AlgebraicSpace
