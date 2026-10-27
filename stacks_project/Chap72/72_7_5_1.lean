/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Picard
import StacksCheckRecall

/-!
# Equation 72.7.5.1

The canonical comparison homomorphism from the Picard group of a locally
Noetherian integral algebraic space to its Weil divisor class group.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- 72.7.5.1: On a locally Noetherian integral algebraic space `X` over a scheme `S`,
the Weil-divisor-class construction for invertible `𝒪_X`-modules induces a canonical
homomorphism of abelian groups `X.PicardGroup ⟶ WeilDivisorClassGroup X` sending the
class of an invertible module to its Weil divisor class. -/
@[stacks 0EPW] #check
  (AlgebraicGeometry.AlgebraicSpace.picardToWeilDivisorClassGroup X :
    X.PicardGroup →+ WeilDivisorClassGroup X)
