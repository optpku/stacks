/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Topology.ExtremallyDisconnected

/-!
# Stone-Cech compactification bridges
-/

@[expose] public section

universe u

open Topology

namespace StoneCech

variable {X : Type u} [TopologicalSpace X]

/-- For a locally compact Hausdorff space, the Stone-Cech unit is an open embedding. -/
@[stacks 090A "the Stone-Cech unit identifies a locally compact Hausdorff space with an open subspace"]
theorem isOpenEmbedding_unit [LocallyCompactSpace X] [T2Space X] :
    IsOpenEmbedding (stoneCechUnit : X → StoneCech X) := sorry

/-- The Stone-Cech compactification of a discrete space is extremally disconnected. -/
@[stacks 090C "Stone-Cech compactification of a discrete space is extremally disconnected"]
instance extremallyDisconnected [DiscreteTopology X] :
    ExtremallyDisconnected (StoneCech X) := sorry

end StoneCech
