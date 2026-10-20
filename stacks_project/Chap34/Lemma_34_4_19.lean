/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' T T' : Scheme.{u}}
variable (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
variable (sq : IsPullback g' f' f g)

/- Lemma 34.4.19 (1): for a cartesian square of schemes, pulling the big étale direct image
`f_{big,*}` back along the relocalization morphism `i_g` agrees with first pulling back along
`i_{g'}` and then applying the small étale direct image `f'_{small,*}`. -/
@[stacks 0DDA] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.pushforwardBaseChange_isomorphic f g f' g' sq :
    IsIsomorphic
      ((Etale.Big.morphismOfTopoi f) _* ⋙
        (Etale.SmallToBig.morphismOfTopoi g)⁻¹)
      ((Etale.SmallToBig.morphismOfTopoi g')⁻¹ ⋙
        (Etale.SmallToBig.smallMorphism f') _*))

/- Lemma 34.4.19 (2): for a cartesian square of schemes, pulling the big étale direct image
`f_{big,*}` back along `g_{big}` agrees with first pulling back along `g'_{big}` and then applying
the big étale direct image `f'_{big,*}`. -/
@[stacks 0DDA] #check
  (CategoryTheory.GrothendieckTopology.Over.BaseChange.map_isIso
      Scheme.etaleTopology g' f' f g sq :
    IsIso
      (CategoryTheory.GrothendieckTopology.Over.BaseChange.map
        Scheme.etaleTopology g' f' f g sq.w))

end AlgebraicGeometry.Scheme
