/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeneralLinear.Determinant

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

section

variable (S : Scheme.{u}) (B : AlgebraicSpace S) (n : ℕ) [NeZero n]

/- Example 78.7.5: for `B → S` as in Section 78.3 and `n ≥ 1`, the determinant is a morphism of
group algebraic spaces `GLₙ,B ⟶ 𝔾ₘ,B` over `B`, obtained as the base change of the determinant
morphism `GLₙ,S ⟶ 𝔾ₘ[S]` over `S` from Groupoids, Example 39.5.5. -/
@[stacks 043N] #check
  (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.Determinant.hom B n :
    AlgebraicGeometry.AlgebraicSpace.GeneralLinear.groupSpace B n ⟶
      AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.groupSpace B)

end
