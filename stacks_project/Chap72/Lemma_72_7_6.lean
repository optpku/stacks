/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap72.«72_7_5_1_Picard»
public import stacks_project.Chap66.Lemma_66_25_4_Normal

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
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- Lemma 72.7.6: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. If `X` is normal, then the comparison homomorphism
`(72.7.5.1)` `picardToWeilDivisorClassGroup X : X.PicardGroup →+ WeilDivisorClassGroup X`
from `Pic(X)` to `Cl(X)` is injective. -/
@[stacks 0EPX]
theorem injective_picardToWeilDivisorClassGroup [IsNormal X] :
    Function.Injective (picardToWeilDivisorClassGroup X) :=
  sorry

/-- The comparison homomorphism from the Picard group to the Weil divisor class
group of a normal locally Noetherian integral algebraic space has trivial kernel. -/
theorem picardToWeilDivisorClassGroup_eq_zero_iff [IsNormal X] (x : X.PicardGroup) :
    picardToWeilDivisorClassGroup X x = 0 ↔ x = 0 :=
  sorry

/-- An invertible module on a normal locally Noetherian integral algebraic space
has trivial Weil divisor class if and only if its Picard class is trivial. -/
theorem invertibleModuleWeilDivisorClass_eq_zero_iff [IsNormal X]
    (L : X.Modules) [isInvertibleObject L] :
    invertibleModuleWeilDivisorClass L = 0 ↔ Modules.picardClass L = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
