/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.IrreducibleCloseds.Hausdorff
public import ReasLib.Topology.Sober.Hausdorff
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

/-!
# Example 5.8.13

Mathlib owns the Hausdorff and irreducibility characterizations.  ReasLib adds
the bundled irreducible-closed singleton result and the convenient sober-space
bridge, each at its corresponding mathematical owner.
-/

/- Example 5.8.13 (1): Hausdorff spaces have disjoint open neighborhoods for distinct points. -/
@[stacks 004Y "Hausdorff spaces via disjoint open neighborhoods"]
#check @t2Space_iff

/- Example 5.8.13 (2): irreducible subsets of Hausdorff spaces are singletons. -/
@[stacks 004Y "irreducible subsets of Hausdorff spaces are singletons"]
#check @isIrreducible_iff_singleton

/- Example 5.8.13 (2): irreducible closed subsets of Hausdorff spaces are bundled singletons. -/
@[stacks 004Y "irreducible closed subsets of Hausdorff spaces are singletons"]
#check @TopologicalSpace.IrreducibleCloseds.exists_eq_singleton

/- Example 5.8.13 (3): every Hausdorff space is sober. -/
@[stacks 004Y "Hausdorff spaces are sober"]
#check @T2Space.sober
