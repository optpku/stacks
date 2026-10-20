/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic

@[expose] public section

universe u v

/-!
# Definition 34.6.1

This chapter entry is a compatibility facade for syntomic covering families.
-/

/- Definition 34.6.1: `AlgebraicGeometry.SyntomicCover` is the fixed-target
cover owner; `AlgebraicGeometry.Scheme.SyntomicCovering` is its indexed-family
counterpart. -/
@[stacks 0225] #check (AlgebraicGeometry.SyntomicCover.{u, v} :
  (T : AlgebraicGeometry.Scheme.{u}) → Type (max (u + 1) (v + 1)))
#check AlgebraicGeometry.SyntomicCover.source_spec
#check AlgebraicGeometry.Scheme.SyntomicCovering
