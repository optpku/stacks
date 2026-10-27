/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Picard.Normal
import StacksCheckRecall

/-!
# Injectivity of the Picard-to-class-group comparison

On a locally Noetherian integral algebraic space that is normal, the comparison
homomorphism from the Picard group to the Weil divisor class group is injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X] [IsNormal X]

/- Lemma 72.7.6: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. If `X` is normal, then the comparison homomorphism
`(72.7.5.1)` `picardToWeilDivisorClassGroup X : X.PicardGroup →+ WeilDivisorClassGroup X`
from `Pic(X)` to `Cl(X)` is injective. -/
@[stacks 0EPX]
#check (AlgebraicGeometry.AlgebraicSpace.injective_picardToWeilDivisorClassGroup X :
    Function.Injective (picardToWeilDivisorClassGroup X))

variable (x : X.PicardGroup)

#check (AlgebraicGeometry.AlgebraicSpace.picardToWeilDivisorClassGroup_eq_zero_iff X x :
    picardToWeilDivisorClassGroup X x = 0 ↔ x = 0)

variable (L : X.Modules) [isInvertibleObject L]

#check (AlgebraicGeometry.AlgebraicSpace.invertibleModuleWeilDivisorClass_eq_zero_iff X L :
    invertibleModuleWeilDivisorClass L = 0 ↔ Modules.picardClass L = 0)

end AlgebraicGeometry.AlgebraicSpace
