/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NonMcQuillan

/-!
# A non-McQuillan affine formal algebraic space
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 110.75.1: there exists an affine formal algebraic space which is not
McQuillan. -/
@[stacks 0CBC] #check (AlgebraicGeometry.exists_isAffineFormalAlgebraicSpace_not_isMcQuillan :
  ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
    (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
    (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
    (X : Sheaf (𝒮.bigTopology S) (Type (u+1))),
    IsAffineFormalAlgebraicSpace X ∧ ¬ IsMcQuillan X)

end AlgebraicGeometry
