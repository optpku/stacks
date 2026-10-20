/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Lift.Functoriality

/-!
# Identity and composition comparisons for bilimit lifts

Universal lifts into bilimit pseudocones are canonical only up to invertible `2`-morphism.
This file supplies their identity and composition comparisons, together with computation
rules after applying the represented comparison functor.

These isomorphisms are the shape-independent functoriality infrastructure used when a
shape-specific limit construction turns universal lifts into maps between chosen limit
objects.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u wJ vJ uJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {F : J ⥤ᵖ B}

/-- The image of the identity apex map under a pseudocone comparison is canonically the
cone itself. -/
noncomputable abbrev lift.id.comparisonIso (S : PseudoCone F) :
    (S.comparison S.pt).obj (𝟙 S.pt) ≅ S.π :=
  ColaxCostructuredArrow.IsUniversal.lift.id.comparisonIso S

/-- The represented comparison of two successive universal maps is canonically the source
pseudocone.

This is the composition computation underlying functorial use of bilimit lifts. -/
noncomputable abbrev lift.comp.comparisonIso (R S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (T.comparison R.pt).obj (lift R S ≫ lift S T) ≅ R.π :=
  ColaxCostructuredArrow.IsUniversal.lift.comp.comparisonIso R S T

/-- The universal self-map of a bilimit apex is canonically isomorphic to its identity map. -/
noncomputable abbrev lift.id.iso (S : PseudoCone F) [S.IsBilimit] :
    𝟙 S.pt ≅ lift S S :=
  ColaxCostructuredArrow.IsUniversal.lift.id.iso S

/-- Successive universal maps between bilimit pseudocones compose to the universal map between
their endpoints. -/
noncomputable abbrev lift.comp.iso (R S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    lift R S ≫ lift S T ≅ lift R T :=
  ColaxCostructuredArrow.IsUniversal.lift.comp.iso R S T

/-- The represented forward cell of the universal identity comparison is the canonical
identity-cone presentation followed by the inverse chosen lift comparison. -/
@[simp]
theorem lift.id.iso.map_hom (S : PseudoCone F) [S.IsBilimit] :
    (S.comparison S.pt).map (lift.id.iso S).hom =
      (lift.id.comparisonIso S ≪≫
        (lift.comparisonIso S S).symm).hom := sorry

/-- The represented inverse cell of the universal identity comparison is the inverse
canonical presentation composite. -/
@[simp]
theorem lift.id.iso.map_inv (S : PseudoCone F) [S.IsBilimit] :
    (S.comparison S.pt).map (lift.id.iso S).inv =
      (lift.id.comparisonIso S ≪≫
        (lift.comparisonIso S S).symm).inv := sorry

/-- The represented forward cell of the universal composition comparison is the canonical
composite presentation followed by the inverse endpoint lift comparison. -/
@[simp]
theorem lift.comp.iso.map_hom (R S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (T.comparison R.pt).map (lift.comp.iso R S T).hom =
      (lift.comp.comparisonIso R S T ≪≫
        (lift.comparisonIso R T).symm).hom := sorry

/-- The represented inverse cell of the universal composition comparison is the inverse
canonical presentation composite. -/
@[simp]
theorem lift.comp.iso.map_inv (R S T : PseudoCone F)
    [S.IsBilimit] [T.IsBilimit] :
    (T.comparison R.pt).map (lift.comp.iso R S T).inv =
      (lift.comp.comparisonIso R S T ≪≫
        (lift.comparisonIso R T).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

All four non-`Prop` declarations are transparent specializations of the generic
`ColaxCostructuredArrow.IsUniversal` functoriality API. The constant-diagram identity and
composition constraints enter only through that pseudofunctor specialization; this file makes
no additional choice. -/

end Bicategory.PseudoCone

end CategoryTheory
