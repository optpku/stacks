/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.HomologicalKernel.Retract
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ] [HasZeroMorphisms D]
variable {A : Type u₂} [Category.{v₂} A]
variable (H : D ⥤ A)

/- Lemma 13.6.3: a homological kernel is closed under direct summands.  The reusable owner is
retract stability, which does not require `H` to be homological. -/
@[stacks 05RD] #check
  (Functor.homologicalKernel_of_biprod (F := H) :
    ∀ {X Y : D} [HasBinaryBiproduct X Y],
      H.homologicalKernel (X ⊞ Y) →
        H.homologicalKernel X ∧ H.homologicalKernel Y)

/- Owner-level formulation used by subsequent quotient arguments. -/
#check (inferInstance : H.homologicalKernel.IsStableUnderRetracts)

/- Strict fullness follows canonically from retract stability. -/
#check (inferInstance : H.homologicalKernel.IsClosedUnderIsomorphisms)
