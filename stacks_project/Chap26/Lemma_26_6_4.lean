/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.GlobalSections.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.6.4: maps from a locally ringed space to an affine scheme are
equivalent to contravariant maps on global sections. -/
@[stacks 01I1] #check LocallyRingedSpace.GlobalSections.homEquivAffine
#check LocallyRingedSpace.GlobalSections.homEquivAffine_apply
#check LocallyRingedSpace.GlobalSections.homEquivAffine_symm_apply
