/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFppf
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 34.7.5

This chapter entry is a compatibility facade for finite standard fppf
covering families.
-/

/- Definition 34.7.5: a standard fppf covering of an affine scheme is a finite
family of affine sources whose maps are flat and locally of finite presentation
and whose images jointly cover the target. -/
@[stacks 021Q] #check
  (AlgebraicGeometry.StandardFppfCover.{u} :
    ∀ (T : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine T], Type (u + 1))
#check AlgebraicGeometry.StandardFppfCover.source_spec
#check AlgebraicGeometry.StandardFppfCover.toFppfCover
