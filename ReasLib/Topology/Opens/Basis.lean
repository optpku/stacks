/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Basis
public import ReasLib.Topology.Opens.QuasiCompact

/-!
# Topological bases and the canonical site of opens

This file translates ordinary basis and compactness hypotheses into the generic site-level
properties used by sheaf presentation theorems.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

variable {X : Type u} [TopologicalSpace X]

/-- A topological basis supplies enough selected objects for the canonical Grothendieck topology
on `Opens X`. -/
theorem IsBasis.hasEnoughObjects {B : Set (Opens X)} (hB : IsBasis B) :
    (Opens.grothendieckTopology X).HasEnoughObjectsWithProperty
      (fun U : Opens X ↦ U ∈ B) := sorry

/-- If every selected open is compact, the selected objects are quasi-compact in the canonical
Grothendieck site of opens. -/
theorem basisIsQuasiCompact {B : Set (Opens X)}
    (hcompact : ∀ U, U ∈ B → IsCompact (U : Set X)) :
    CategoryTheory.GrothendieckTopology.Basis.IsQuasiCompact
      (Opens.grothendieckTopology X) B := sorry

end TopologicalSpace.Opens
