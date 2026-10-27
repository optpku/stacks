/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

variable {S : Scheme.{u}}

/-- A morphism factors through another morphism when it is 2-isomorphic to a
composite through that morphism. -/
def FactorsThrough {X Y Z : GroupoidsOver S} (f : Y ⟶ X) (ι : Z ⟶ X) : Prop :=
  ∃ g : Y ⟶ Z, Nonempty (g ≫ ι ≅ f)

/-- Factoring through a morphism is equivalent to a 2-isomorphic factorization. -/
theorem factorsThrough_iff {X Y Z : GroupoidsOver S} (f : Y ⟶ X) (ι : Z ⟶ X) :
    FactorsThrough f ι ↔ ∃ g : Y ⟶ Z, Nonempty (g ≫ ι ≅ f) := sorry

end AlgebraicGeometry.Groupoids.Hom
