/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangle
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ] [ShiftCompatibility R A]
variable [HasShift (K R A) ℤ]
variable [(Comp.inKFunctor : Comp R A ⥤ K R A).CommShift ℤ]
variable {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting)

/- Lemma 22.27.1 (09P6): a graded-split short complex in a differential graded category with
compatible shifts determines its canonical triangle in the DG homotopy category. -/
@[stacks 09P6] #check
  (AdmissibleBoundary.triangleInK σ : Triangle (K R A))

/- All three consecutive composites in the canonical triangle vanish. -/
#check @AdmissibleBoundary.triangleInK_comp_zero₁₂
#check @AdmissibleBoundary.triangleInK_comp_zero₂₃
#check @AdmissibleBoundary.triangleInK_comp_zero₃₁

/- The owner retains both standard formulas `π d s` and `-d(π) s` for the boundary. -/
#check @AdmissibleBoundary.raw
#check @AdmissibleBoundary.raw_eq_negDifferential
