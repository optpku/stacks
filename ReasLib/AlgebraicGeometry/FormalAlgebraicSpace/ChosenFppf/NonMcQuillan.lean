/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan

/-!
# Non-McQuillan affine formal algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- At a sufficiently large chosen big fppf site, there is an affine formal
algebraic space whose directed affine thickening presentations cannot all have
surjective inverse-limit projections on global sections. -/
theorem exists_isAffineFormalAlgebraicSpace_not_isMcQuillan :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X : Sheaf (𝒮.bigTopology S) (Type (u+1))),
      IsAffineFormalAlgebraicSpace X ∧ ¬ IsMcQuillan X := sorry

end AlgebraicGeometry
