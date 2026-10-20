/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology classes which vanish locally

Local vanishing is a property of a section of any additive presheaf, independent of the origin of
that presheaf. This leaf provides that fine-grained predicate for comparison and descent APIs.
-/

open CategoryTheory
open Opposite

universe u v w

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- A section of an additive presheaf is locally zero for `J` if it restricts to zero on every
member of some `J`-cover. -/
@[stacks 0EZC "locally zero presheaf section"]
def IsLocallyZero
    (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {U : C} (ξ : G.obj (op U)) : Prop :=
  ∃ T : J.Cover U, ∀ I : T.Arrow, (G.map I.f.op) ξ = 0

/-- The defining cover characterization of `Presheaf.IsLocallyZero`. -/
@[stacks 0EZC "locally zero cover criterion"]
theorem isLocallyZero_iff
    (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {U : C} (ξ : G.obj (op U)) :
    IsLocallyZero J G ξ ↔
      ∃ T : J.Cover U, ∀ I : T.Arrow, (G.map I.f.op) ξ = 0 :=
  Iff.rfl

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{max u v} C]

/-- Positive-degree cohomology classes of an abelian sheaf are locally zero. -/
@[stacks 01FW "positive cohomology classes are locally zero"]
theorem cohomology_isLocallyZero_of_positive
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    (F : Sheaf J AddCommGrpCat.{max u v}) {U : C} {n : ℕ} (hn : 0 < n)
    (ξ : F.H' n U) :
    Presheaf.IsLocallyZero J (F.cohomologyPresheaf n) ξ := sorry

/-- The cover form of positive-degree local cohomology vanishing. -/
@[stacks 01FW "positive cohomology classes admit a vanishing cover"]
theorem exists_cover_restrict_eq_zero_of_positive_cohomology_class
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    (F : Sheaf J AddCommGrpCat.{max u v}) {U : C} {n : ℕ} (hn : 0 < n)
    (ξ : F.H' n U) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      (((F.cohomologyPresheaf n).map I.f.op) ξ = 0) := sorry

end CategoryTheory.Sheaf

end
