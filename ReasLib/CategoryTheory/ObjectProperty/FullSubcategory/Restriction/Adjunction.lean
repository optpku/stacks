/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Adjunctions restricted to object-property full subcategories

The restriction is built from the canonical inclusion comparisons, so the
result is genuine adjunction data rather than an existential wrapper.
-/

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.FullSubcategory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Restrict an adjunction to full subcategories preserved by its left and
right adjoints. -/
@[stacks 001D "adjunction on object-property full subcategories"]
noncomputable def adjunction
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (hF : P ≤ Q.inverseImage F) (hG : Q ≤ P.inverseImage G) :
    restrict F hF ⊣ restrict G hG :=
  adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (restrict.compιIso F hF).symm (restrict.compιIso G hG).symm

end CategoryTheory.ObjectProperty.FullSubcategory

end
