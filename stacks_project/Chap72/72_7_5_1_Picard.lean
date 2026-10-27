/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Picard

/-!
# Picard comparison with the Weil divisor class group

The canonical comparison homomorphism sends the class of an invertible module
on a locally Noetherian integral algebraic space to its Weil divisor class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- 72.7.5.1: The Picard-to-Weil-divisor-class comparison homomorphism. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.picardToWeilDivisorClassGroup X :
    X.PicardGroup →+ WeilDivisorClassGroup X)
