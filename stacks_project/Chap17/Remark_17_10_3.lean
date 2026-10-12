/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Remark 17.10.3 (02CF): an infinite coproduct of quasi-coherent module sheaves need not be
quasi-coherent. -/
@[stacks 02CF]
#check
  (existsInfiniteCoproductNotQuasicoherent.{u} :
    ∃ (X : RingedSpace.{u}) (I : Type u) (_ : Infinite I)
      (F : I → RingedSpace.Modules X),
      (∀ i, (F i).IsQuasicoherent) ∧ ¬ (∐ F).IsQuasicoherent)
