module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Lift

/-!
# Universal lifts into a bilimit pseudocone

The represented comparison of a bilimit pseudocone is an equivalence of categories. Its chosen
quasi-inverse supplies universal apex maps and `2`-morphisms. This file encapsulates that choice
behind comparison and uniqueness isomorphisms, so downstream code need not unfold the selected
inverse functor.

The construction is shape-independent and depends only on the Yoneda-style `IsBilimit`
property; it does not use the concrete morphism representation of the pseudocone bicategory.
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

/-- The chosen quasi-inverse to the comparison represented by a bilimit pseudocone.

This is the functorial owner of universal lifts with a fixed source apex: objects are strong
transformations `Pseudofunctor.const J X ⟶ F`, morphisms are modifications, and their images
are respectively apex maps and `2`-morphisms into `T.pt`. -/
noncomputable abbrev lift.functor (T : PseudoCone F) [T.IsBilimit] (X : B) :
    (Pseudofunctor.const J X ⟶ F) ⥤ (X ⟶ T.pt) :=
  ColaxCostructuredArrow.IsUniversal.lift.functor T X

/-- Comparing a lifted map recovers the original cone transformation, naturally in
modifications. -/
noncomputable abbrev lift.counitIso (T : PseudoCone F) [T.IsBilimit] (X : B) :
    lift.functor T X ⋙ T.comparison X ≅ 𝟭 (Pseudofunctor.const J X ⟶ F) :=
  ColaxCostructuredArrow.IsUniversal.lift.counitIso T X

/-- Lifting the comparison of an apex map recovers that map, naturally in its
`2`-morphisms. -/
noncomputable abbrev lift.unitIso (T : PseudoCone F) [T.IsBilimit] (X : B) :
    𝟭 (X ⟶ T.pt) ≅ T.comparison X ⋙ lift.functor T X :=
  ColaxCostructuredArrow.IsUniversal.lift.unitIso T X

/-- Mapping a modification by `lift.functor` and comparing it again is conjugation by the
canonical comparison isomorphisms. -/
@[simp]
theorem lift.functor.comparison_map (T : PseudoCone F) [T.IsBilimit]
    {X : B} {η θ : Pseudofunctor.const J X ⟶ F} (Γ : η ⟶ θ) :
    (T.comparison X).map ((lift.functor T X).map Γ) =
      (lift.counitIso T X).hom.app η ≫ Γ ≫
        (lift.counitIso T X).inv.app θ := sorry

/-- Lifting a represented `2`-morphism is conjugation by the canonical isomorphisms from an
apex map to the lift of its comparison. -/
@[simp]
theorem lift.functor.map_comparison (T : PseudoCone F) [T.IsBilimit]
    {X : B} {l m : X ⟶ T.pt} (γ : l ⟶ m) :
    (lift.functor T X).map ((T.comparison X).map γ) =
      (lift.unitIso T X).inv.app l ≫ γ ≫
        (lift.unitIso T X).hom.app m := sorry

/-- A chosen universal map from a pseudocone `S` to a bilimit pseudocone `T`.

This is the shape-independent owner specialized by readable limit-shape APIs such as
`PseudoPullbackCone.lift`. It chooses a preimage of `S.π` under the represented comparison
equivalence; clients should use `lift.comparisonIso` and `lift.uniqueIso` rather than unfold
that choice. -/
noncomputable abbrev lift (S T : PseudoCone F) [T.IsBilimit] :
    S.pt ⟶ T.pt :=
  ColaxCostructuredArrow.IsUniversal.lift S T

/-- The object action of `lift.functor` on a pseudocone transformation is its universal
apex map. -/
@[simp]
theorem lift.functor.obj (S T : PseudoCone F) [T.IsBilimit] :
    (lift.functor T S.pt).obj S.π = lift S T := sorry

/-- The represented comparison sends the chosen universal map to the source pseudocone.

This is the primary specification of `PseudoCone.lift`. -/
noncomputable abbrev lift.comparisonIso (S T : PseudoCone F) [T.IsBilimit] :
    (T.comparison S.pt).obj (lift S T) ≅ S.π :=
  ColaxCostructuredArrow.IsUniversal.lift.comparisonIso S T

/-- Any other apex map presenting `S` under the represented comparison is canonically
isomorphic to `lift S T`. -/
noncomputable abbrev lift.uniqueIso (S T : PseudoCone F) [T.IsBilimit]
    (l : S.pt ⟶ T.pt) (e : (T.comparison S.pt).obj l ≅ S.π) :
    l ≅ lift S T :=
  ColaxCostructuredArrow.IsUniversal.lift.uniqueIso S T l e

/-- Applying the represented comparison to the forward cell of `lift.uniqueIso` recovers the
specified presentation followed by the inverse chosen lift comparison. -/
@[simp]
theorem lift.uniqueIso.map_hom (S T : PseudoCone F) [T.IsBilimit]
    (l : S.pt ⟶ T.pt) (e : (T.comparison S.pt).obj l ≅ S.π) :
    (T.comparison S.pt).map (lift.uniqueIso S T l e).hom =
      (e ≪≫ (lift.comparisonIso S T).symm).hom := sorry

/-- Applying the represented comparison to the inverse cell of `lift.uniqueIso` recovers the
inverse of the specified presentation composite. -/
@[simp]
theorem lift.uniqueIso.map_inv (S T : PseudoCone F) [T.IsBilimit]
    (l : S.pt ⟶ T.pt) (e : (T.comparison S.pt).obj l ≅ S.π) :
    (T.comparison S.pt).map (lift.uniqueIso S T l e).inv =
      (e ≪≫ (lift.comparisonIso S T).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

All non-`Prop` choices in this file are transparent specializations of
`ColaxCostructuredArrow.IsUniversal`'s quasi-inverse, unit, counit, and uniqueness API. Public
clients are insulated from the chosen inverse by `lift.comparisonIso`, `lift.uniqueIso`, and their
map computations; no second choice, raw `Classical.choice`, or existential witness is exposed. -/

end Bicategory.PseudoCone

end CategoryTheory
