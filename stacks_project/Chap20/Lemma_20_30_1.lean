module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Godement.Homotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicTopology
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace.Godement

/- [stacks 0FKS] Lemma 20.30.1: For a ringed space `X`, the Godement monad associated
to pullback to the family of all points and the product of the corresponding skyscraper
modules gives a functorial resolution

`0 ⟶ F ⟶ step X ⋙ F ⟶ (step X)^[2] ⋙ F ⟶ ⋯`.

Every term of the resulting cochain complex is flasque.  After applying the canonical
stalk functor at any `x : X`, its augmentation is a chain homotopy equivalence; in
particular, the augmentation is a quasi-isomorphism. -/
#check @adjunction
#check @monad
#check @step
#check @unit
#check @multiplication
#check @augmented
#check @cosimplicial
#check @complex
#check @augmentation
#check @cosimplicial_obj
#check @complex_obj_X
#check @augmentation_app_f_zero
#check @augmentation_app_f_succ
#check @complexTerm_isFlasque
#check @discreteEquiv
#check @pointEquiv
#check @stalkAugmentation
#check @stalkAugmentation_homotopyEquivalence
@[stacks 0FKS] #check @augmentation_quasiIso

end AlgebraicGeometry.RingedSpace.Godement
