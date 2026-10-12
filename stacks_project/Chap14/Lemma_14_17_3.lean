/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Constant
import StacksCheckRecall

/-!
@stack 017K
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasFiniteLimits C]
variable (U : SSet.{w}) [U.ObjFinite] [U.Nonempty]
variable (T : SimplicialObject C)
variable [U.EventuallyDegenerate]

/- Lemma 14.17.3 (017K): a finite dimension bound reduces the constant-object restriction of
the mapping presheaf to finite-limit data, so finite limits suffice for representability. -/
@[stacks 017K]
#check (constRestriction.isRepresentable.ofEventuallyDegenerate U T :
  Functor.IsRepresentable (constRestriction U T))

end CategoryTheory.SimplicialObject.internalHom
