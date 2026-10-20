/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import ReasLib.CategoryTheory.Limits.Colimit.Concrete.Finite

/-!
# Monomorphism diagrams and filtered colimits of modules

The forgetful functor from modules preserves filtered colimits.  Consequently elements have stage
representatives, and a diagram made entirely of monomorphisms has monomorphic coprojections into
its colimit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ModuleCat.FilteredColimits

variable {R : Type u} [Ring R]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (B : J ⥤ ModuleCat.{max v u, u} R)

/-- Every element of a filtered colimit of modules comes from an element at one stage. -/
theorem exists_ι_preimage
    (z : (CategoryTheory.Limits.colimit B : ModuleCat.{max v u, u} R)) :
    ∃ (j : J) (x : B.obj j), (colimit.ι B j).hom x = z := sorry

/-- A finite family of elements of a filtered colimit of modules has representatives at one
common stage. -/
theorem exists_ι_preimage_finite {α : Type*} [Finite α]
    (z : α → (CategoryTheory.Limits.colimit B : ModuleCat.{max v u, u} R)) :
    ∃ (j : J) (x : α → B.obj j),
      ∀ a, (colimit.ι B j).hom (x a) = z a := sorry

/-- Equality of two representatives in a filtered colimit of modules is equivalent to equality
after transition to one common stage. -/
theorem rep_eq_iff_exists {i j : J} (x : B.obj i) (y : B.obj j) :
    (colimit.ι B i).hom x = (colimit.ι B j).hom y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
        (B.map f).hom x = (B.map g).hom y := sorry

/-- Finitely many equalities between representatives at two stages of a filtered colimit of
modules can be witnessed by one common pair of transition maps. -/
theorem exists_rep_eq_finite {α : Type*} [Finite α] {i j : J}
    (x : α → B.obj i) (y : α → B.obj j)
    (h : ∀ a, (colimit.ι B i).hom (x a) = (colimit.ι B j).hom (y a)) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
      ∀ a, (B.map f).hom (x a) = (B.map g).hom (y a) := sorry

/-- If every transition map of a filtered module diagram is mono, every coprojection into its
colimit is mono. -/
theorem ι_mono_of_map_mono
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (B.map f)) (j : J) :
    Mono (colimit.ι B j) := sorry

end ModuleCat.FilteredColimits
