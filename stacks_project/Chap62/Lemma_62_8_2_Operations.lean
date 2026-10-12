/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Operations

/-!
# Restriction, flat pullback, and proper pushforward of fibre cycle families

The reusable family-level operations are owned by
`AlgebraicGeometry.RelativeCycle`.
-/

#check AlgebraicGeometry.RelativeCycle.restrictFiberMap
#check AlgebraicGeometry.RelativeCycle.restrict_locallyFiniteSupport
#check AlgebraicGeometry.RelativeCycle.restrictCycle
#check AlgebraicGeometry.RelativeCycle.restrictCycle_mem_dimensionSubgroup
#check AlgebraicGeometry.RelativeCycle.restrict
#check AlgebraicGeometry.RelativeCycle.restrict_apply
#check AlgebraicGeometry.RelativeCycle.flatPullbackFiberMap
#check AlgebraicGeometry.RelativeCycle.flatPullback_locallyFiniteSupport
#check AlgebraicGeometry.RelativeCycle.flatPullbackCycle
#check AlgebraicGeometry.RelativeCycle.flatPullbackCycle_mem_dimensionSubgroup
#check AlgebraicGeometry.RelativeCycle.flatPullback
#check AlgebraicGeometry.RelativeCycle.flatPullback_apply
#check AlgebraicGeometry.RelativeCycle.pushforwardFiberMap
#check AlgebraicGeometry.RelativeCycle.instIsProper_pushforwardFiberMap
#check AlgebraicGeometry.RelativeCycle.pushforward
#check AlgebraicGeometry.RelativeCycle.pushforward_apply
