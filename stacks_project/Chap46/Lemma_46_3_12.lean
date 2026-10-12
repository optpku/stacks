/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Colimits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

#check
  (ModuleValuedFunctor.TensorAdequate.coproduct :
    ∀ (A : CommRingCat.{u}) {ι : Type u}
      (F : ι → ModuleValuedFunctor.bundled.{u, u} A) (c : Cofan F),
      IsColimit c → (∀ i, ModuleValuedFunctor.TensorAdequate (F i)) →
        ModuleValuedFunctor.TensorAdequate c.pt)

/- Lemma 46.3.12: an arbitrary direct sum of adequate functors on `Alg_A` is
adequate, and a colimit of adequate functors is adequate. -/
@[stacks 06V4] #check
  (ModuleValuedFunctor.TensorAdequate.closedUnderColimitsOfShape :
    ∀ (A : CommRingCat.{u}) (J : Type u) [SmallCategory J],
      ObjectProperty.IsClosedUnderColimitsOfShape
        (ModuleValuedFunctor.TensorAdequate (A := A)) J)

end ModuleValuedFunctor
