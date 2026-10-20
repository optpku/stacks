module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell.Functor.Source
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward two-cells after localization

This file owns localization extension of source-level pushforward transformations and the
resulting Hom functor.
-/

@[expose] public section

universe uC uD uS uT vC vD vS vT

namespace CategoryTheory.Functor.Pushforward

open Limits
open scoped Bicategory Functor

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C}

/-- The natural transformation between explicitly certified localized pushforward maps. It is
the unique extension of the source-level transformation along the localization functor. -/
@[stacks 04WI "localized pushforward two-cell"]
noncomputable def map₂
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q}
    (hF : sourceMap.inverts u F) (hG : sourceMap.inverts u G)
    (eta : F ⟶ G) : map u F hF ⟶ map u G hG :=
  Localization.Construction.natTransExtension
    ((map.comparisonIso u F hF).hom ≫
      Functor.whiskerRight (sourceMap₂ u eta) (u.pushforwardFractions q).Q ≫
        (map.comparisonIso u G hG).inv)

/-- The localized pushforward `2`-cell formed from a bundled inversion family.  This is the
proof-family-facing owner corresponding to `map.ofInversionChoice`; the explicit `map₂` above
remains available when a consumer needs to pin the two proof terms separately. -/
@[stacks 04WI "localized pushforward two-cell from inversion choice"]
noncomputable def map₂.ofInversionChoice
    (u : C ⥤ D) (h : InversionChoice u p q)
    {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    map.ofInversionChoice u F h ⟶ map.ofInversionChoice u G h :=
  map₂ u (h.inverts F) (h.inverts G) eta

/-- Restricting the localized pushforward `2`-cell along the localization functor recovers the
source-level transformation, with the canonical comparison transports. -/
@[stacks 04WI "localized pushforward two-cell localization comparison"]
theorem map₂.compQ
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q}
    (hF : sourceMap.inverts u F) (hG : sourceMap.inverts u G)
    (eta : F ⟶ G) :
    Functor.whiskerLeft (u.pushforwardFractions p).Q (map₂ u hF hG eta) =
      (map.comparisonIso u F hF).hom ≫
        Functor.whiskerRight (sourceMap₂ u eta) (u.pushforwardFractions q).Q ≫
          (map.comparisonIso u G hG).inv := sorry

/-- Component form of `map₂.compQ`, for rewriting a localized pushforward `2`-cell on an object
coming from the prelocalized source. -/
@[simp, stacks 04WI "localized pushforward two-cell component"]
theorem map₂.compQ_app
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q}
    (hF : sourceMap.inverts u F) (hG : sourceMap.inverts u G)
    (eta : F ⟶ G) (A : u ₚₚ p) :
    (map₂ u hF hG eta).app ((u.pushforwardFractions p).Q.obj A) =
      (map.comparisonIso u F hF).hom.app A ≫
        (u.pushforwardFractions q).Q.map ((sourceMap₂ u eta).app A) ≫
          (map.comparisonIso u G hG).inv.app A := sorry

/-- The localization comparison readout for a `2`-cell formed from an inversion family. -/
@[stacks 04WI "localized pushforward chosen two-cell localization comparison"]
theorem map₂.ofInversionChoice.compQ
    (u : C ⥤ D) (h : InversionChoice u p q)
    {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    Functor.whiskerLeft (u.pushforwardFractions p).Q
        (map₂.ofInversionChoice u h eta) =
      (map.comparisonIso u F (h.inverts F)).hom ≫
        Functor.whiskerRight (sourceMap₂ u eta) (u.pushforwardFractions q).Q ≫
          (map.comparisonIso u G (h.inverts G)).inv := sorry

/-- The object component of the localization comparison readout for a chosen inversion family. -/
@[simp, stacks 04WI "localized pushforward chosen two-cell component"]
theorem map₂.ofInversionChoice.compQ_app
    (u : C ⥤ D) (h : InversionChoice u p q)
    {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) (A : u ₚₚ p) :
    (map₂.ofInversionChoice u h eta).app ((u.pushforwardFractions p).Q.obj A) =
      (map.comparisonIso u F (h.inverts F)).hom.app A ≫
        (u.pushforwardFractions q).Q.map ((sourceMap₂ u eta).app A) ≫
          (map.comparisonIso u G (h.inverts G)).inv.app A := sorry

/-- The chosen localized pushforward `2`-cell preserves identity transformations. -/
@[simp, stacks 04WI "localized pushforward chosen two-cell identity"]
theorem map₂.ofInversionChoice.id
    (u : C ⥤ D) (h : InversionChoice u p q) (F : CartesianBasedFunctor p q) :
    map₂.ofInversionChoice u h (𝟙 F) =
      𝟙 (map.ofInversionChoice u F h) := sorry

/-- The chosen localized pushforward `2`-cell preserves vertical composition. -/
@[simp, stacks 04WI "localized pushforward chosen two-cell composition"]
theorem map₂.ofInversionChoice.comp
    (u : C ⥤ D) (h : InversionChoice u p q)
    {F G H : CartesianBasedFunctor p q} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂.ofInversionChoice u h (eta ≫ theta) =
      map₂.ofInversionChoice u h eta ≫ map₂.ofInversionChoice u h theta := sorry

/-- Localized pushforward preserves identity transformations. -/
@[simp, stacks 04WI "localized pushforward two-cell identity"]
theorem map₂.id (u : C ⥤ D) (F : CartesianBasedFunctor p q)
    (hF : sourceMap.inverts u F) :
    map₂ u hF hF (𝟙 F) = 𝟙 (map u F hF) := sorry

/-- Localized pushforward preserves vertical composition of transformations. -/
@[simp, stacks 04WI "localized pushforward two-cell composition"]
theorem map₂.comp
    (u : C ⥤ D) {F G H : CartesianBasedFunctor p q}
    (hF : sourceMap.inverts u F) (hG : sourceMap.inverts u G)
    (hH : sourceMap.inverts u H)
    (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ u hF hH (eta ≫ theta) =
      map₂ u hF hG eta ≫ map₂ u hG hH theta := sorry

/-- Localized pushforward acts functorially on cartesian based functors and their vertical
transformations. -/
@[stacks 04WI "localized pushforward Hom functor"]
noncomputable def mapFunctor (u : C ⥤ D) (h : InversionChoice u p q) :
    CartesianBasedFunctor p q ⥤ (u ₚ p ⥤ u ₚ q) where
  obj F := map.ofInversionChoice u F h
  map {_ _} eta := map₂.ofInversionChoice u h eta
  map_id F := map₂.ofInversionChoice.id u h F
  map_comp eta theta := map₂.ofInversionChoice.comp u h eta theta

/-- The object action of the localized pushforward Hom functor uses the supplied inversion
proof. -/
@[simp, stacks 04WI "localized pushforward Hom functor object"]
theorem mapFunctor.obj (u : C ⥤ D) (h : InversionChoice u p q)
    (F : CartesianBasedFunctor p q) :
    (mapFunctor u h).obj F = map u F (h.inverts F) := sorry

/-- The morphism action of the localized pushforward hom functor is `map₂`. -/
@[simp, stacks 04WI "localized pushforward Hom functor map"]
theorem mapFunctor.map
    (u : C ⥤ D) (h : InversionChoice u p q)
    {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    (mapFunctor u h).map eta =
      map₂.ofInversionChoice u h eta := sorry

end CategoryTheory.Functor.Pushforward

-- Data audit: localization inversion proofs are explicit inputs to both owners.
