module

public import stacks_project.Chap61.Lemma_61_12_18_BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}}
variable {S S' T T' : X.carrier}
variable (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
variable (sq : IsPullback g' f' f g)

/- Lemma 61.12.18 (1): for a cartesian square in a chosen big pro-étale site,
pulling the big direct image `f_big,*` back along the relocalization `i_g`
agrees with first pulling back along `i_g'` and then applying the small
direct image `f'_small,*`. -/
@[stacks 0F61] #check
  (BaseChange.smallToBigComparison_isIso.{u, v, max u v} f g f' g' sq :
    IsIso (BaseChange.smallToBigComparison.{u, v, max u v} f g f' g' sq))

/- Lemma 61.12.18 (2): for a cartesian square in a chosen big pro-étale site,
pulling the big direct image `f_big,*` back along `g_big` agrees with first
pulling back along `g'_big` and then applying the big direct image
`f'_big,*`. -/
@[stacks 0F61] #check
  (CategoryTheory.GrothendieckTopology.Over.BaseChange.map_isIso
      X.toGrothendieck g' f' f g sq :
    IsIso
      (CategoryTheory.GrothendieckTopology.Over.BaseChange.map
        X.toGrothendieck g' f' f g sq.w))

end AlgebraicGeometry.ChosenBigProetaleSite
