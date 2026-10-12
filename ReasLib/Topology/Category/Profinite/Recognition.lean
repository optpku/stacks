/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Recognition of Profinite Spaces

The bundled category `Profinite` is Mathlib's canonical owner.  This module
provides the unbundled recognition theorem used when a topological-space
statement naturally quantifies over a homeomorphism to a profinite space.
-/

@[expose] public section

universe u

namespace Profinite

variable (X : Type u) [TopologicalSpace X]

/-- A topological space is homeomorphic to a profinite space exactly when it is
Hausdorff, compact, and totally disconnected. -/
@[stacks 08ZY "profinite recognition"]
theorem exists_homeomorph_iff_t2Space_compactSpace_totallyDisconnectedSpace :
    (∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) ↔
      T2Space X ∧ CompactSpace X ∧ TotallyDisconnectedSpace X := sorry

/-- A compact Hausdorff totally disconnected space has a profinite model. -/
theorem exists_homeomorph_of_t2Space_compactSpace_totallyDisconnectedSpace
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X] :
    ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P) := sorry

end Profinite
