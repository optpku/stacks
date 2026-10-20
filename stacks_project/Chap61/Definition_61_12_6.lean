/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardProetale
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 61.12.6

This chapter entry is a compatibility facade for finite standard pro-étale
chart covers of affine schemes.
-/

/- Definition 61.12.6: a standard pro-étale covering of an affine scheme is a
finite family of affine weakly étale maps whose images cover the target. -/
@[stacks 098E] #check
  (AlgebraicGeometry.StandardProetaleCover :
    ∀ (T : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine T], Type (u + 1))
#check AlgebraicGeometry.StandardProetaleCover.source_spec
#check AlgebraicGeometry.StandardProetaleCover.ofAffineFamily
