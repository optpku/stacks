/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ProjectiveDimension.Syzygy
import StacksCheckRecall

/-!
# Projectivity of a Top Syzygy

@stack 00O5
-/

@[expose] public section

@[stacks 00O5 "(1), e = 0"]
#check @LinearMap.ker_projective_of_surjective

@[stacks 00O5 "(2), positive length"]
#check @LinearMap.topKernel_projective_of_exact_of_dimLE

@[stacks 00O5 "natural top-syzygy bound"]
#check @LinearMap.topKernel_projective_of_exact
