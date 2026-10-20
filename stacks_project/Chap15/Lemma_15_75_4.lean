/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Triangulated
import StacksCheckRecall

/-!
# Lemma 15.75.4

@stack 066R

Perfect objects in `DerivedCategory (ModuleCat R)` satisfy two-out-of-three for distinguished
triangles.  The reusable owner is `DerivedCategory.IsPerfect.isTriangulated`; the three typed
checks below record every source-facing orientation.
-/

@[expose] public section

noncomputable section

open CategoryTheory Pretriangulated

universe u

variable (R : Type u) [Ring R]

/- Lemma 15.75.4 (066R), in the three source-facing two-out-of-three forms. -/
@[stacks 066R "third vertex"]
#check
  (DerivedCategory.IsPerfect.obj₃ :
    (T : Triangle (DerivedCategory (ModuleCat R))) →
      T ∈ distTriang (DerivedCategory (ModuleCat R)) →
      T.obj₁.IsPerfect → T.obj₂.IsPerfect →
      T.obj₃.IsPerfect)

@[stacks 066R "second vertex"]
#check
  (DerivedCategory.IsPerfect.obj₂ :
    (T : Triangle (DerivedCategory (ModuleCat R))) →
      T ∈ distTriang (DerivedCategory (ModuleCat R)) →
      T.obj₁.IsPerfect → T.obj₃.IsPerfect →
      T.obj₂.IsPerfect)

@[stacks 066R "first vertex"]
#check
  (DerivedCategory.IsPerfect.obj₁ :
    (T : Triangle (DerivedCategory (ModuleCat R))) →
      T ∈ distTriang (DerivedCategory (ModuleCat R)) →
      T.obj₂.IsPerfect → T.obj₃.IsPerfect →
      T.obj₁.IsPerfect)

#check @DerivedCategory.IsPerfect.isTriangulated
#check @DerivedCategory.IsPerfect.shift
#check @CochainComplex.IsBoundedFiniteProjective.shift
#check @CochainComplex.IsBoundedFiniteProjective.mappingCone
