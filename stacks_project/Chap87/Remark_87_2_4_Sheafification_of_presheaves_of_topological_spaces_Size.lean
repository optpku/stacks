/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Opposites
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Size of a topological-space-valued presheaf

The size of a presheaf of topological spaces is the supremum of the cardinalities
of its values, matching the source formula `|H| = sup_U |H(U)|`.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite
open scoped Cardinal

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- The size of a `TopCat`-valued presheaf, as the supremum of the cardinalities of
its underlying spaces. -/
noncomputable def topCatSize (F : Cᵒᵖ ⥤ TopCat.{max u v}) : Cardinal.{max u v} :=
  ⨆ U : C, #(F.obj (op U))

/-- Unfolding of `topCatSize`. -/
theorem topCatSize_def (F : Cᵒᵖ ⥤ TopCat.{max u v}) :
    topCatSize F = ⨆ U : C, #(F.obj (op U)) :=
  sorry

/-- Each value of a `TopCat`-valued presheaf is bounded in cardinality by `topCatSize`. -/
theorem le_topCatSize (F : Cᵒᵖ ⥤ TopCat.{max u v}) (U : C) :
    #(F.obj (op U)) ≤ topCatSize F :=
  sorry

end CategoryTheory.Presheaf
