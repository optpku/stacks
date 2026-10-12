/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Basis.Comparison
public import ReasLib.Topology.Sheaves.Basis.Extension

/-!
# Extension of set-valued basis sheaves

Concrete extension data is owned by `BasisSiteSheaf.extend`.  This file records the invariant
existence-and-uniqueness statement for the source-style basis-cover predicate without selecting
data through an unproved comparison theorem.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

variable {X : TopCat.{u}} {B : Set (Opens X)}

namespace BasisSheaf

/-- A sheaf of sets on a topological basis extends to a sheaf on the whole space,
uniquely up to a unique isomorphism compatible with restriction maps. -/
@[stacks 009N "basis sheaf extends uniquely up to unique isomorphism"]
theorem existsExtensionUniqueUpToUniqueIso (F : BasisSheaf.{u, max u v} B)
    (hB : Opens.IsBasis B) :
    ∃ E : BasisPresheaf.Extension F.obj,
      ∀ G : BasisPresheaf.Extension F.obj,
        ∃! e : E.sheaf ≅ G.sheaf, BasisPresheaf.Extension.IsCompatibleIso E G e := sorry

end BasisSheaf
