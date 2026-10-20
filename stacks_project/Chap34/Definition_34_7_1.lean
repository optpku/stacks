/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf

@[expose] public section

universe u v

/-!
# Definition 34.7.1

This chapter entry is a compatibility facade for fppf covering families.
-/

/- Definition 34.7.1: an fppf covering is represented by the fixed-target
owner `AlgebraicGeometry.FppfCover`, with an indexed-family companion view. -/
@[stacks 021M] #check (AlgebraicGeometry.FppfCover.{u, v} :
    (T : AlgebraicGeometry.Scheme.{u}) → Type (max (u + 1) (v + 1)))
#check AlgebraicGeometry.FppfCover.source_spec
#check AlgebraicGeometry.Scheme.FppfCovering
