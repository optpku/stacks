/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty.Basic
public import ReasLib.CategoryTheory.Presheaf.UniqueSections
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Sections over sheaf-theoretically empty objects

This leaf converts a covering bottom sieve into terminality of a sheaf's
section object.  It is independent of sheafification and representables.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

namespace IsSheafTheoreticallyEmpty

/-- A sheaf evaluated at a sheaf-theoretically empty object is terminal in its target category. -/
noncomputable abbrev isTerminal_app {A : Type w} [Category A] {J : GrothendieckTopology C} {U : C}
    (hU : J.IsSheafTheoreticallyEmpty U) (F : Sheaf J A) :
    IsTerminal (F.obj.obj (op U)) :=
  F.isTerminalOfBotCover U hU

/-- A type-valued sheaf has a unique section over a sheaf-theoretically empty object. -/
theorem uniqueSections {J : GrothendieckTopology C} {U : C}
    (hU : J.IsSheafTheoreticallyEmpty U) (F : Sheaf J (Type w)) :
    Nonempty (Unique (F.obj.obj (op U))) := sorry

/-- Type-valued sheaves have unique sections on sheaf-theoretically empty objects. -/
instance hasUniqueSectionsOn {J : GrothendieckTopology C} (F : Sheaf J (Type w)) :
    Presheaf.HasUniqueSectionsOn F.obj J.IsSheafTheoreticallyEmpty := sorry

/-- An abelian-group-valued sheaf has a unique section over a sheaf-theoretically empty object. -/
theorem uniqueAddCommGrpSections {J : GrothendieckTopology C} {U : C}
    (hU : J.IsSheafTheoreticallyEmpty U) (F : Sheaf J AddCommGrpCat.{w}) :
    Nonempty (Unique (F.obj.obj (op U))) := sorry

end IsSheafTheoreticallyEmpty

end CategoryTheory.GrothendieckTopology
