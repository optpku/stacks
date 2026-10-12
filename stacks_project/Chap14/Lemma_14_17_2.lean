/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Constant
import StacksCheckRecall

/-!
@stack 017J
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasCountableLimits C]
variable (U : SSet.{w}) [U.ObjFinite] [U.Nonempty]
variable (T : SimplicialObject C)

/- Lemma 14.17.2 (017J): the constant-object restriction of the mapping presheaf from a
degreewise finite nonempty simplicial set is representable when the target category has binary
coproducts and countable limits. The canonical `U.Nonempty` assumption is definitionally the
source condition `Nonempty (U _⦋0⦌)`. -/
@[stacks 017J]
#check (constRestriction.isRepresentable.ofCountableLimits U T :
  Functor.IsRepresentable (constRestriction U T))

end CategoryTheory.SimplicialObject.internalHom
