/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

namespace CategoryTheory.Sheaf

/-- If a topological space has at most two points, every positive-degree global
sheaf cohomology object of every abelian sheaf on it is zero. -/
theorem isZero_higherCohomology_of_enatCard_le_two
    (X : TopCat.{u}) (hX : ENat.card X ≤ 2) (F : X.Sheaf AddCommGrpCat.{u})
    (i : ℕ) (hi : 0 < i) :
    IsZero (F.H' i (⊤ : Opens X)) := sorry

/-- There is a three-point topological space carrying an abelian sheaf with
nonzero first global sheaf cohomology. -/
theorem exists_threePoint_abelianSheaf_nonzero_firstCohomology :
    ∃ (X : TopCat.{u}) (F : X.Sheaf AddCommGrpCat.{u}),
      ENat.card X = 3 ∧ ¬ IsZero (F.H' 1 (⊤ : Opens X)) := sorry

end CategoryTheory.Sheaf
