/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Basis.Cover

/-!
# The sheaf condition on a topological basis

This file compares the explicit basis-cover condition with the canonical sheaf condition for
the induced Grothendieck topology.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

namespace CategoryTheory.Presheaf

/-- The explicit basis-cover condition for a topological basis is equivalent to the canonical
sheaf condition for the induced Grothendieck topology. -/
theorem isBasisSheaf_iff_isSheaf (hB : Opens.IsBasis B)
    (F : (BasisOpen B)ᵒᵖ ⥤ Type v) :
    IsBasisSheaf F ↔ IsSheaf (basisGrothendieckTopology B) F := sorry

end CategoryTheory.Presheaf
