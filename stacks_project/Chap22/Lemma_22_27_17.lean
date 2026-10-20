/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCones

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DifferentialGradedCategory R A] [DifferentialGradedCategory R B]
variable [HasShift (Comp R A) ℤ] [HasShift (Comp R B) ℤ]
variable [HasShift (K R A) ℤ] [HasShift (K R B) ℤ]
variable [((Comp.inKFunctor : Comp R A ⥤ K R A)).CommShift ℤ]
variable [((Comp.inKFunctor : Comp R B ⥤ K R B)).CommShift ℤ]
variable [HasZeroObject (K R A)] [HasZeroObject (K R B)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]
variable [∀ n : ℤ, (shiftFunctor (K R B) n).Additive]
variable [PA : Pretriangulated (K R A)] [PB : Pretriangulated (K R B)]
variable (F : DgFunctor R A B) [F.mapK.CommShift ℤ]
variable {BA : CompBoundaryAssignment R A} {BB : CompBoundaryAssignment R B}
variable (CA : BA.AdmissibleCones) (CB : BB.AdmissibleCones)
variable (hA : CA.Presents PA) (hB : CB.Presents PB)
variable (hF : F.MapsCones CA CB)

/- Lemma 22.27.17 (0FQF): a shift-compatible DG functor between categories whose triangulations
are presented by admissible-cone systems is exact when it maps source cones to target cones. -/
@[stacks 0FQF]
#check
  (DifferentialGradedCategory.DgFunctor.mapK_isTriangulated F CA CB hA hB hF :
    F.mapK.IsTriangulated)

-- Construction-facing bridge: the canonical cone-generated pretriangulations need no separate
-- `Presents` witnesses.
#check @DifferentialGradedCategory.DgFunctor.mapK_isTriangulated_of_coneSystems
