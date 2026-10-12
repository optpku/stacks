/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Types.Constant
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace TopCat
open scoped TopCat

universe u

noncomputable section

/-
The constant sheaf is represented by the canonical sheafification of
`(Functor.const (Opens X)ᵒᵖ).obj A`. Thus
`CategoryTheory.toSheafify` supplies the source map, while
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` supplies exactly its stalkwise
isomorphism. The only unmatched source clause is the identification of `A` with the stalk of the
constant presheaf, exposed below through the canonical global germ map rather than a parallel
constant-sheaf wrapper.
-/

variable (X : TopCat.{u}) (A : Type u)

/- Example 6.11.3 (1): the canonical map from the constant presheaf with value `A` to the
constant sheaf with value `A` is the sheafification unit.
-/
@[stacks 007B "constant presheaf to constant sheaf"]
#check CategoryTheory.toSheafify
  (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A)

/- Example 6.11.3 (2): for every `x : X`, the canonical germ map identifies `A` with the stalk
of the constant presheaf `(Functor.const (Opens X)ᵒᵖ).obj A` at `x`. -/
@[stacks 007B "value of the constant presheaf stalk"]
#check TopCat.Presheaf.Constant.stalk_bijective X A

/- Example 6.11.3 (3): functoriality of stalks sends the sheafification unit to an isomorphism
from the constant-presheaf stalk to the constant-sheaf stalk.
-/
@[stacks 007B "stalk map induced by sheafification"]
#check fun x : X ↦
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u)
    ((Functor.const (Opens X)ᵒᵖ).obj A)

/- Example 6.11.3 (4): the canonical composite identifies `A` with the stalk at `x` of the
constant sheaf with value `A`. -/
@[stacks 007B "value of the constant sheaf stalk"]
#check TopCat.Sheaf.Constant.toStalk_isIso X A
