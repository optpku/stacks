/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit.Preserves
public import ReasLib.CategoryTheory.Limits.Colimit.Concrete.Finite

/-!
# Representatives in filtered colimits of commutative algebras

This file specializes the generic concrete filtered-colimit API to commutative algebras over a
fixed base ring. It hides the forgetful-functor preservation instance from downstream users.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CommAlgCat.FilteredColimits

variable {k : Type u} [CommRing k]
variable {J : Type v} [SmallCategory J] [IsFiltered J] [UnivLE.{v, u}]
variable (F : J ⥤ CommAlgCat.{u} k) [HasColimit F]

/-- Every element of a filtered colimit of commutative algebras comes from one stage. -/
theorem exists_rep (x : (colimit F : CommAlgCat.{u} k)) :
    ∃ (j : J) (y : F.obj j), colimit.ι F j y = x := sorry

/-- Equality of two representatives in a filtered colimit of commutative algebras is equivalent
to equality after transition to one common stage. -/
theorem rep_eq_iff_exists {i j : J} (x : F.obj i) (y : F.obj j) :
    colimit.ι F i x = colimit.ι F j y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := sorry

/-- A finite family of elements of a filtered colimit of commutative algebras has representatives
at one common stage. -/
theorem exists_rep_finite {α : Type*} [Finite α]
    (x : α → (colimit F : CommAlgCat.{u} k)) :
    ∃ (j : J) (y : α → F.obj j),
      ∀ a, colimit.ι F j (y a) = x a := sorry

/-- Finitely many equalities between representatives at two stages of a filtered colimit of
commutative algebras can be witnessed by one common pair of transition maps. -/
theorem exists_rep_eq_finite {α : Type*} [Finite α] {i j : J}
    (x : α → F.obj i) (y : α → F.obj j)
    (h : ∀ a, colimit.ι F i (x a) = colimit.ι F j (y a)) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
      ∀ a, F.map f (x a) = F.map g (y a) := sorry

end CommAlgCat.FilteredColimits
