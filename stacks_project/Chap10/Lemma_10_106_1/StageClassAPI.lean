/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass
import StacksCheckRecall

@[expose] public section

/-!
# Associated-graded stage support for Lemma 10.106.1

The quotient-Rees stage-class and degree-piece comparison API used by Lemma 10.106.1 is owned by
`ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass`.

@stack 00NO
-/

@[stacks 00NO "homogeneous stage class"]
#check @Ideal.AssociatedGraded.stageClass

@[stacks 00NO "stage-class membership in the homogeneous grade"]
#check @Ideal.AssociatedGraded.stageClass_mem_grade

@[stacks 00NO "multiplication of homogeneous stage classes"]
#check @Ideal.AssociatedGraded.stageClass_mul

@[stacks 00NO "linear stage-class presentation"]
#check @Ideal.AssociatedGraded.stageClassLinear

@[stacks 00NO "vanishing criterion for a stage class"]
#check @Ideal.AssociatedGraded.stageClass_eq_zero_iff

@[stacks 00NO "homogeneous grade and successive quotient comparison"]
#check @Ideal.AssociatedGraded.gradeEquivPiece

@[stacks 00NO "degree-piece comparison on stage classes"]
#check @Ideal.AssociatedGraded.gradeEquivPiece_stageClassLinear
