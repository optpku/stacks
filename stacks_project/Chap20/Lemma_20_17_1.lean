/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange.BoundedBelow
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

/- Lemma 20.17.1 (02N7): for a commutative square of ringed spaces whose horizontal maps
`g : S' ⟶ S` and `g' : X' ⟶ X` are both flat, every `K : D⁺(X.Modules)` has the canonical
base-change map `g^* Rf_* K ⟶ R(f')_* (g')^* K` in `D⁺(S'.Modules)`. -/
@[stacks 02N7] #check @RingedSpace.Hom.BoundedBaseChange.map

#check @RingedSpace.Hom.BoundedBaseChange.app
#check @RingedSpace.Hom.BoundedBaseChange.IsMap
#check @RingedSpace.Hom.BoundedBaseChange.IsMapAt
#check @RingedSpace.Hom.BoundedBaseChange.map_isMap
#check @RingedSpace.Hom.BoundedBaseChange.map_isMapAt
#check @RingedSpace.Hom.BoundedBaseChange.IsMap.eq_map
#check @RingedSpace.Hom.BoundedBaseChange.IsMapAt.eq_app
#check @RingedSpace.Hom.BoundedBaseChange.app_naturality
