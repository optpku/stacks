/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardSyntomic

@[expose] public section

universe u

/-!
# Definition 34.6.5

This chapter entry is a compatibility facade for finite standard syntomic
covering families.
-/

/- Definition 34.6.5: use `AlgebraicGeometry.StandardSyntomicCovering`, with
the explicit `toAffineFamily` and `toSyntomicCover` computation APIs. -/
@[stacks 0229] #check (AlgebraicGeometry.StandardSyntomicCovering.{u} :
  ∀ (T : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine T], Type (u + 1))
#check AlgebraicGeometry.StandardSyntomicCovering.toAffineFamily
#check AlgebraicGeometry.StandardSyntomicCovering.toSyntomicCover
