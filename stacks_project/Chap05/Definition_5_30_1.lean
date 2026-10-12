/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

universe u v

/- Definition 5.30.1 (1): a topological group is a group with continuous multiplication and
inversion; this is exactly the canonical mathlib class `IsTopologicalGroup`. -/
@[stacks 0B1Z "topological groups have continuous multiplication and inversion"]
#check IsTopologicalGroup

variable (G : Type u) (H : Type v) [TopologicalSpace G] [Group G]
  [TopologicalSpace H] [Group H]

/- Definition 5.30.1 (2): a homomorphism of topological groups is a group homomorphism whose
underlying map is continuous; mathlib bundles these as `ContinuousMonoidHom`, written `G →ₜ* H`. -/
@[stacks 0B1Z "continuous homomorphisms of topological groups"]
#check (G →ₜ* H)
