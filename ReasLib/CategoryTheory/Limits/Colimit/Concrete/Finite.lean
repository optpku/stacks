/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import ReasLib.CategoryTheory.Limits.Colimit.Concrete.Basic

/-!
# Finite families in concrete filtered colimits

Finite families of elements of a preserved filtered colimit can be represented at one common
stage. Likewise, finitely many equalities between two fixed stages can be witnessed after one
common pair of transition maps. The indexing type only needs a `Finite` instance.
-/

@[expose] public section

open CategoryTheory

universe w vC uC vJ uJ

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
variable {C : Type uC} [Category.{vC} C]

/-- Equality of two representatives in a preserved filtered colimit cocone is equivalent to
equality after transition to one common stage. -/
theorem IsColimit.rep_eq_iff_exists (U : C ⥤ Type w) (B : J ⥤ C)
    {c : Cocone B} (hc : IsColimit c) [PreservesColimit B U]
    {i j : J} (x : U.obj (B.obj i)) (y : U.obj (B.obj j)) :
    U.map (c.ι.app i) x = U.map (c.ι.app j) y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
        U.map (B.map f) x = U.map (B.map g) y := sorry

/-- Equality of two representatives in a preserved canonical filtered colimit is equivalent to
equality after transition to one common stage. -/
theorem colimit_rep_eq_iff_exists (U : C ⥤ Type w) (B : J ⥤ C)
    [HasColimit B] [PreservesColimit B U]
    {i j : J} (x : U.obj (B.obj i)) (y : U.obj (B.obj j)) :
    U.map (colimit.ι B i) x = U.map (colimit.ι B j) y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
        U.map (B.map f) x = U.map (B.map g) y := sorry

/-- A finite family of elements of the point of a preserved colimit cocone has representatives
at one common stage. -/
theorem IsColimit.exists_ι_preimage_finite (U : C ⥤ Type w) (B : J ⥤ C)
    {c : Cocone B} (hc : IsColimit c) [PreservesColimit B U]
    {α : Type*} [Finite α] (x : α → U.obj c.pt) :
    ∃ (j : J) (y : α → U.obj (B.obj j)),
      ∀ a, U.map (c.ι.app j) (y a) = x a := sorry

/-- A finite family of elements of a preserved canonical colimit has representatives at one
common stage. -/
theorem exists_colimit_ι_preimage_finite (U : C ⥤ Type w) (B : J ⥤ C)
    [HasColimit B] [PreservesColimit B U]
    {α : Type*} [Finite α] (x : α → U.obj (colimit B)) :
    ∃ (j : J) (y : α → U.obj (B.obj j)),
      ∀ a, U.map (colimit.ι B j) (y a) = x a := sorry

/-- Finitely many equalities between representatives at two fixed stages of a preserved
filtered colimit cocone admit one common pair of transition maps witnessing all of them. -/
theorem IsColimit.exists_rep_eq_finite (U : C ⥤ Type w) (B : J ⥤ C)
    {c : Cocone B} (hc : IsColimit c) [PreservesColimit B U]
    {α : Type*} [Finite α] {i j : J}
    (x : α → U.obj (B.obj i)) (y : α → U.obj (B.obj j))
    (h : ∀ a, U.map (c.ι.app i) (x a) = U.map (c.ι.app j) (y a)) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
      ∀ a, U.map (B.map f) (x a) = U.map (B.map g) (y a) := sorry

/-- Finitely many equalities between representatives at two fixed stages of a preserved
canonical filtered colimit admit one common pair of transition maps witnessing all of them. -/
theorem exists_colimit_rep_eq_finite (U : C ⥤ Type w) (B : J ⥤ C)
    [HasColimit B] [PreservesColimit B U]
    {α : Type*} [Finite α] {i j : J}
    (x : α → U.obj (B.obj i)) (y : α → U.obj (B.obj j))
    (h : ∀ a, U.map (colimit.ι B i) (x a) =
      U.map (colimit.ι B j) (y a)) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
      ∀ a, U.map (B.map f) (x a) = U.map (B.map g) (y a) := sorry

end CategoryTheory.Limits
