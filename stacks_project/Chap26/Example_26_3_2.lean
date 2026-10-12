/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

variable (X : LocallyRingedSpace.{u}) (U : Opens X)

/- The stalk of an open restriction is canonically the ambient stalk. -/
@[stacks 01HF "stalk of an open restriction"]
#check X.restrictStalkIso U.isOpenEmbedding
#check X.restrictStalkIso_inv_eq_ofRestrict U.isOpenEmbedding
#check X.ofRestrict_stalkMap_isIso

/- Example 26.3.2: the inclusion of an open restriction is an open
immersion. -/
@[stacks 01HF] #check LocallyRingedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding
