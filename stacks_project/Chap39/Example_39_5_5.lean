/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GeneralLinear.Determinant

universe u

open AlgebraicGeometry

section

variable (n : ℕ)

/- Example 39.5.5 (1): The determinant defines a morphism of group schemes
`GL n ⟶ 𝔾ₘ` over `Spec (ULift ℤ)`. -/
@[stacks 022X] #check
  (AlgebraicGeometry.GeneralLinear.Determinant.hom (ULift.{u} (Fin n)) :
    GeneralLinear.groupScheme (ULift.{u} ℤ) (ULift.{u} (Fin n)) ⟶ (𝔾ₘ).toGrp)

end

section

variable (S : Scheme.{u}) (n : ℕ)

/- Example 39.5.5 (2): Base change gives a determinant morphism
`GL(n, S) ⟶ 𝔾ₘ[S]` over every scheme `S`. -/
@[stacks 022X] #check
  (AlgebraicGeometry.GeneralLinear.Determinant.baseChange S (ULift.{u} (Fin n)) :
    GeneralLinear.baseChange (specULiftZIsTerminal.from S) (ULift.{u} (Fin n)) ⟶
      (𝔾ₘ[S]).toGrp)

end
