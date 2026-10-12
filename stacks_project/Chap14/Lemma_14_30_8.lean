/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration.HomotopyEquiv
import StacksCheckRecall

/-!
@stack 08NS
-/

@[expose] public section

open CategoryTheory
open SSet.modelCategoryQuillen

universe u

namespace SSet.modelCategoryQuillen.I

variable {X Y : SSet.{u}} (f : X ⟶ Y) (hf : I.rlp f)

/- Lemma 14.30.8 (08NS): a trivial Kan fibration is a simplicial homotopy equivalence. -/
@[stacks 08NS]
#check (I.rlp.le_homotopyEquivalences f hf :
  SimplicialObject.IsHomotopyEquivalence f)

#check I.rlp.isHomotopyEquivalence hf

#check I.rlp.splitEpi hf

#check I.rlp.homotopyEquiv hf

end SSet.modelCategoryQuillen.I
