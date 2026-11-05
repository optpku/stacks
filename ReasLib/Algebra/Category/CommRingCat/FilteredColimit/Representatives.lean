/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import ReasLib.CategoryTheory.Limits.Colimit.Concrete.Finite

/-!
# Representatives in filtered colimits of commutative rings

This file specializes the generic concrete filtered-colimit API to Mathlib's explicit
mixed-universe colimit cocone for `CommRingCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CommRingCat.FilteredColimits

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- A chosen filtered colimit cocone of nontrivial commutative rings has a
nontrivial cocone point if the forgetful functor preserves this colimit.
This allows unrelated index and carrier universes; preservation is automatic
for filtered diagrams small relative to the carrier universe. -/
theorem nontrivial_of_isColimit
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [PreservesColimit F (forget CommRingCat.{u})]
    [∀ j, Nontrivial (F.obj j)] :
    Nontrivial c.pt := by
  classical
  let i := (IsFiltered.nonempty (C := J)).some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h ↦ ?_⟩
  obtain ⟨k, f, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat.{u}) hc) _ _).mp h
  exact zero_ne_one (((F.map f).hom.map_zero.symm.trans e).trans (F.map f).hom.map_one)

variable (F : J ⥤ CommRingCat.{max v u})

/-- A filtered colimit of nontrivial commutative rings is nontrivial, including
the mixed-universe model used by `CommRingCat.FilteredColimits`. -/
theorem nontrivial_of_all [∀ j, Nontrivial (F.obj j)] :
    Nontrivial (colimit F) := sorry

/-- Every element of the explicit filtered colimit of commutative rings comes from one stage. -/
theorem exists_rep (x : colimit F) :
    ∃ (j : J) (y : F.obj j), (colimitCocone F).ι.app j y = x := sorry

/-- Equality of two representatives in the explicit filtered colimit is equivalent to equality
after transition to one common stage. -/
theorem rep_eq_iff_exists {i j : J} (x : F.obj i) (y : F.obj j) :
    (colimitCocone F).ι.app i x = (colimitCocone F).ι.app j y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := sorry

/-- A finite family of elements of the explicit filtered colimit has representatives at one
common stage. -/
theorem exists_rep_finite {α : Type*} [Finite α] (x : α → colimit F) :
    ∃ (j : J) (y : α → F.obj j),
      ∀ a, (colimitCocone F).ι.app j (y a) = x a := sorry

/-- Finitely many equalities between representatives at two stages of the explicit filtered
colimit can be witnessed by one common pair of transition maps. -/
theorem exists_rep_eq_finite {α : Type*} [Finite α] {i j : J}
    (x : α → F.obj i) (y : α → F.obj j)
    (h : ∀ a, (colimitCocone F).ι.app i (x a) =
      (colimitCocone F).ι.app j (y a)) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
      ∀ a, F.map f (x a) = F.map g (y a) := sorry

end CommRingCat.FilteredColimits
