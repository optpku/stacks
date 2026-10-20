/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Coordinate.Syzygy
import StacksCheckRecall

/-!
# Projective Dimension and Projective Resolutions

@stack 0CXC
-/

@[expose] public section

@[stacks 0CXC "coordinate projective resolution length"]
#check @CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate.HasLengthLE

@[stacks 0CXC "projective-dimension and kernel-syzygy TFAE"]
#check @CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate.projectiveDimensionLE_tfae_kernelSyzygy
