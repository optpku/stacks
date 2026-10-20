/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.GlobalSections
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Torsors on topological spaces

This leaf specializes the site-generic torsor API to the opens site of a
topological space.  It exposes the local-section formulation used by
geometric applications without making the generic `CategoryTheory.Sheaf.Torsor`
depend on a point-set topology.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.Sheaf.Torsor

variable {X : TopCat.{u}}
variable {G : X.Sheaf GrpCat.{u}}

/-- Definition 20.4.1 [02FO]: the trivial torsor has a section over every open subset. -/
@[stacks 02FO]
theorem nonempty_sections_trivial (U : Opens X) :
    Nonempty ((trivial G).Sections U) := sorry

/-- A torsor section exists after restricting to a sufficiently small open neighborhood of a
point already lying in the given open subset. -/
theorem exists_open_nhdsWithin_nonempty_sections (P : Torsor G) (U : Opens X) {x : X}
    (hx : x ∈ U) :
    ∃ V : Opens X, V ≤ U ∧ x ∈ V ∧ Nonempty (P.Sections V) := sorry

/-- Definition 20.4.1 [02FO]: every point has an open neighborhood on which a torsor has a
section. -/
@[stacks 02FO]
theorem locally_nonempty (P : Torsor G) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ Nonempty (P.Sections U) := sorry

/-- Site-theoretic global sections of a torsor on a topological space are nonempty exactly when
its sections over the top open are nonempty. -/
@[simp, stacks 02FP "topological torsor global sections at the top open"]
theorem nonempty_globalSections_iff_nonempty_sections_top (P : Torsor G) :
    Nonempty ((Sheaf.Γ (Opens.grothendieckTopology X) (Type u)).obj P.carrier) ↔
      Nonempty (P.Sections (⊤ : Opens X)) := sorry

/-- Lemma 20.4.2 (02FP): a torsor on a topological space is trivial if and only if it has a
section over the top open. -/
@[stacks 02FP "topological torsor triviality criterion"]
theorem isTrivial_iff_nonempty_sections_top (P : Torsor G) :
    P.IsTrivial ↔ Nonempty (P.Sections (⊤ : Opens X)) := sorry

end CategoryTheory.Sheaf.Torsor
