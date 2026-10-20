/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory

/-!
# Categories fibred in groupoids associated to presheaves

The discrete Grothendieck construction of a set-valued presheaf over a scheme
gives a category fibred in groupoids over that scheme.
-/

@[expose] public section

open CategoryTheory FiberedCategoryOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The category fibred in groupoids associated to a presheaf with values in
`Type (u + 1)` over a scheme in universe `u`, by the discrete Grothendieck
construction and the canonical inclusion of categories fibred in sets. -/
abbrev ofPresheaf {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F)

/-- The groupoid fibration associated to a presheaf is the discrete
Grothendieck construction viewed as a category fibred in groupoids. -/
theorem ofPresheaf_spec {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    ofPresheaf F =
      (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F) := rfl

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.Scheme.Over

/-- The category fibred in groupoids associated to a set-valued functor on
schemes over `S`, obtained by the discrete Grothendieck construction and
forgetting from sets to groupoids. -/
abbrev toGroupoidsOver {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F)

/-- `toGroupoidsOver F` is the discrete Grothendieck construction of `F`,
forgotten to groupoids. -/
theorem toGroupoidsOver_eq {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    toGroupoidsOver F =
      (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F) :=
  sorry

/-- The projection of `toGroupoidsOver F` is the opposite category-of-elements
projection of `F`. -/
theorem toGroupoidsOver_p {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    (toGroupoidsOver F).p = ((Sets.ofPresheaf (Over S)).obj F).p :=
  sorry

end AlgebraicGeometry.Scheme.Over
