/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Base
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Finiteness after homogeneous localization

@stack 07Z2
-/

/- Lemma 10.57.9 (1): if `S` is of finite type over `R`, then the
degree-zero homogeneous localization `S_(f)` is of finite type over `R` for every
homogeneous `f`. The reusable owner is the base-change bridge in
`HomogeneousLocalization.Away.finiteType_over`. -/
@[stacks 07Z2 "(1)"]
#check @HomogeneousLocalization.Away.finiteType_over

/- Lemma 10.57.9 (2): if `S` is of finite type over `R` and the
graded module `M` is finite over `S`, then the degree-zero homogeneous localization
`M_(f)` is finite over `S_(f)`.  The reusable owner is
`HomogeneousLocalization.Away.Module.finite_of_finiteType`. -/
@[stacks 07Z2 "(2)"]
#check @HomogeneousLocalization.Away.Module.finite_of_finiteType
