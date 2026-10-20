module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map
public import ReasLib.CategoryTheory.Fibered.Pushforward.Unit

/-!
# Naturality of the pushforward unit under source maps

This file constructs the canonical comparison between the pushforward unit followed by a
localized pushforward map and the original source map followed by the target pushforward unit.
The construction is independent of any Hom-category application.
-/

@[expose] public section

universe uC uD uS uT vC vD vS vT

namespace CategoryTheory

open Limits
open scoped Functor

namespace Functor.Pushforward.Prelocalized

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]

/-- The comma-square compatibility for the source comparison on a prelocalized unit object. -/
@[stacks 04WI "prelocalized source comparison comma compatibility"]
theorem mapObjFstIso.w (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (𝟭 D).map (u.map (F.toBasedFunctor.projectionIso.app x).inv) ≫
        (obj u q (F.toFunctor.obj x)).fst.hom =
      (obj u p x).fst.hom ≫ u.map (F.toBasedFunctor.projectionIso.app x).inv := sorry

/-- The explicit comma-object comparison underlying source naturality of the prelocalized
pushforward unit. -/
@[stacks 04WI "prelocalized source comparison comma isomorphism"]
noncomputable def mapObjFstIso (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (obj u p x).fst ≅ (obj u q (F.toFunctor.obj x)).fst :=
  Comma.isoMk
    (u.mapIso (F.toBasedFunctor.projectionIso.app x).symm)
    (F.toBasedFunctor.projectionIso.app x).symm (mapObjFstIso.w u F x)

/-- The pullback compatibility for the explicit source comparison on a prelocalized unit
object. -/
@[stacks 04WI "prelocalized source comparison pullback compatibility"]
theorem mapObjIso.w (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (Comma.snd (𝟭 D) u).map (mapObjFstIso u F x).hom ≫
        (obj u q (F.toFunctor.obj x)).iso.hom =
      ((Functor.Pushforward.sourceMap u F).obj (obj u p x)).iso.hom ≫
        q.map (𝟙 (F.toFunctor.obj x)) := sorry

/-- The explicit source comparison between the image of a prelocalized unit object and the
corresponding target prelocalized unit object. -/
@[stacks 04WI "prelocalized source comparison isomorphism"]
noncomputable def mapObjIso (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (Functor.Pushforward.sourceMap u F).obj (obj u p x) ≅
      obj u q (F.toFunctor.obj x) :=
  CategoricalPullback.mkIso (mapObjFstIso u F x) (Iso.refl _) (mapObjIso.w u F x)

/-- The first forward component of the prelocalized source comparison. -/
@[simp, stacks 04WI "prelocalized source comparison forward comma component"]
theorem mapObjIso.hom.fst (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (mapObjIso u F x).hom.fst = (mapObjFstIso u F x).hom := sorry

/-- The second forward component of the prelocalized source comparison is the identity. -/
@[simp, stacks 04WI "prelocalized source comparison forward base component"]
theorem mapObjIso.hom.snd (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (mapObjIso u F x).hom.snd = 𝟙 (F.toFunctor.obj x) := sorry

/-- The first inverse component of the prelocalized source comparison. -/
@[simp, stacks 04WI "prelocalized source comparison inverse comma component"]
theorem mapObjIso.inv.fst (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (mapObjIso u F x).inv.fst = (mapObjFstIso u F x).inv := sorry

/-- The second inverse component of the prelocalized source comparison is the identity. -/
@[simp, stacks 04WI "prelocalized source comparison inverse base component"]
theorem mapObjIso.inv.snd (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (x : S) :
    (mapObjIso u F x).inv.snd = 𝟙 (F.toFunctor.obj x) := sorry

end Functor.Pushforward.Prelocalized

namespace Functor.Pushforward.Unit

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]

/-- The canonical comparison component between first applying the pushforward unit and then a
localized pushforward map, and first applying the source map and then the target unit. -/
@[stacks 04WI "localized source comparison component"]
noncomputable def mapIsoApp (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) (x : S) :
    (functor u p ⋙ Functor.Pushforward.map u F hF).obj x ≅
      (F.toFunctor ⋙ functor u q).obj x :=
  (Functor.Pushforward.map.comparisonIso u F hF).app
      (Functor.Pushforward.Prelocalized.obj u p x) ≪≫
    (u.pushforwardFractions q).Q.mapIso
      (Functor.Pushforward.Prelocalized.mapObjIso u F x)

/-- The unit-map comparison components are natural in the source object. -/
@[stacks 04WI "localized source comparison naturality"]
theorem mapIsoApp.naturality (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    {x y : S} (f : x ⟶ y) :
    (functor u p ⋙ Functor.Pushforward.map u F hF).map f ≫
        (mapIsoApp u F hF y).hom =
      (mapIsoApp u F hF x).hom ≫ (F.toFunctor ⋙ functor u q).map f := sorry

/-- The pushforward-unit comparison isomorphism for a cartesian based functor with an explicit
source-fraction inversion proof. -/
@[stacks 04WI "localized source comparison isomorphism"]
noncomputable def mapIso (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) :
    functor u p ⋙ Functor.Pushforward.map u F hF ≅
      F.toFunctor ⋙ functor u q :=
  NatIso.ofComponents (mapIsoApp u F hF) (mapIsoApp.naturality u F hF)

/-- The forward component of the pushforward-unit comparison is the localization comparison
followed by the localized prelocalized-object comparison. -/
@[simp, stacks 04WI "localized source comparison forward component"]
theorem mapIso.hom.app (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) (x : S) :
    (mapIso u F hF).hom.app x =
      (Functor.Pushforward.map.comparisonIso u F hF).hom.app
          (Functor.Pushforward.Prelocalized.obj u p x) ≫
        (u.pushforwardFractions q).Q.map
          (Functor.Pushforward.Prelocalized.mapObjIso u F x).hom := sorry

/-- The inverse component of the pushforward-unit comparison is the inverse localized
prelocalized-object comparison followed by the inverse localization comparison. -/
@[simp, stacks 04WI "localized source comparison inverse component"]
theorem mapIso.inv.app (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) (x : S) :
    (mapIso u F hF).inv.app x =
      (u.pushforwardFractions q).Q.map
          (Functor.Pushforward.Prelocalized.mapObjIso u F x).inv ≫
        (Functor.Pushforward.map.comparisonIso u F hF).inv.app
          (Functor.Pushforward.Prelocalized.obj u p x) := sorry

end Functor.Pushforward.Unit

end CategoryTheory

-- Data audit: both comparison isomorphisms own explicit hom and inverse data. Their `sorryAx`
-- dependencies are confined to compatibility and naturality laws.
