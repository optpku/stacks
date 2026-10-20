/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.CartesianHom
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian pushforward maps

This module packages the universe-polymorphic raw pushforward map as a
`CartesianBasedFunctor`.  The fixed-universe `FiberedCategoryOver` map is then a thin conversion
through the standard cartesian Hom equivalence.
-/

@[expose] public section

universe uC uD uS uT vC vD vS vT

namespace CategoryTheory

open Limits

namespace CartesianBasedFunctor.Pushforward

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C} [p.IsFibered] [q.IsFibered]

/-- Lemma 8.12.8 (tag 04WI): the universe-polymorphic cartesian pushforward map induced by an
explicit proof that the source-level map inverts the pushforward fractions. -/
@[stacks 04WI "universe-polymorphic cartesian pushforward map"]
noncomputable def map (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor p q)
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) :
    CartesianBasedFunctor
      (u.pushforwardProjection p hp) (u.pushforwardProjection q hq) :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor
      (Functor.Pushforward.map u F hF)
      (Functor.Pushforward.map.compProjection u hp hq F hF))
    (Functor.Pushforward.map.preservesStronglyCartesian u hp hq F hF)

/-- Forgetting an explicit cartesian pushforward map recovers the based functor induced by the
raw localized pushforward map. -/
@[simp, stacks 04WI "cartesian pushforward based computation"]
theorem map.toBasedFunctor
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor p q)
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) :
    (map u F hp hq hF).toBasedFunctor =
      BasedFunctor.ofFunctor
        (Functor.Pushforward.map u F hF)
        (Functor.Pushforward.map.compProjection u hp hq F hF) := sorry

/-- The total functor underlying an explicit cartesian pushforward map is the raw localized
pushforward map. -/
@[simp, stacks 04WI "cartesian pushforward total computation"]
theorem map.toFunctor
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor p q)
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) :
    (map u F hp hq hF).toFunctor = Functor.Pushforward.map u F hF := sorry

/-- The based functor underlying an explicit cartesian pushforward map preserves strongly
cartesian morphisms. -/
@[stacks 04WI "cartesian pushforward strong cartesian preservation"]
theorem map.preservesStronglyCartesian
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor p q)
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) :
    (map u F hp hq hF).toBasedFunctor.PreservesStronglyCartesian := sorry

/-- The endpoint projection choices and raw map-inversion family needed for pushforward on one
category of cartesian based functors. The map family is inherited from the projection-independent
raw owner. -/
@[stacks 04WI "cartesian pushforward inversion choice"]
structure InversionChoice (u : C ⥤ D) (p : S ⥤ C) (q : T ⥤ C) : Prop extends
    mapChoice : Functor.Pushforward.InversionChoice u p q where
  /-- The projection choice at the source endpoint. -/
  source : Functor.Pushforward.ProjectionChoice u p
  /-- The projection choice at the target endpoint. -/
  target : Functor.Pushforward.ProjectionChoice u q

attribute [stacks 04WI "cartesian pushforward raw inversion choice field"]
  CartesianBasedFunctor.Pushforward.InversionChoice.mapChoice
attribute [stacks 04WI "cartesian pushforward source projection choice field"]
  CartesianBasedFunctor.Pushforward.InversionChoice.source
attribute [stacks 04WI "cartesian pushforward target projection choice field"]
  CartesianBasedFunctor.Pushforward.InversionChoice.target

/-- The raw map-inversion family underlying a cartesian pushforward choice. -/
add_decl_doc InversionChoice.mapChoice

/-- Combine endpoint projection choices with the canonical inversion theorem for source-level
pushforward maps.  This proposition-valued constructor is kept separate from the functor data so
an unfinished proof of canonical inversion does not become a dependency of that data. -/
@[stacks 04WI "cartesian pushforward inversion choice from endpoints"]
theorem InversionChoice.ofProjectionChoices {u : C ⥤ D}
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q) :
    InversionChoice u p q := sorry

/-- The cartesian pushforward map determined by its bundled endpoint and inversion choices. -/
@[stacks 04WI "cartesian pushforward map from inversion choice"]
noncomputable def map.ofInversionChoice
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor p q)
    (h : CartesianBasedFunctor.Pushforward.InversionChoice u p q) :
    CartesianBasedFunctor (u.pushforwardProjection p h.source)
      (u.pushforwardProjection q h.target) :=
  map u F h.source h.target (h.inverts F)

end CartesianBasedFunctor.Pushforward

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}

/-- A fixed-owner inversion family for pushforward on one Hom category of fibred categories.
Unlike `InversionChoice`, this records no endpoint projection choices, so it can be reused when
those choices are already owned by the surrounding objects. -/
@[stacks 04WI "fixed-Hom pushforward inversion family"]
structure MapInversionChoice (u : C ⥤ D)
    (X Y : FiberedCategoryOver.{uC, vC, uS, vS} C) : Prop where
  /-- The chosen inversion proof for each morphism in the fixed Hom category. -/
  inverts (F : X ⟶ Y) : Functor.Pushforward.sourceMap.inverts u
    (FiberedCategoryOver.toCartesianBasedFunctor F)

attribute [stacks 04WI "fixed-Hom pushforward inversion field"]
  FiberedCategoryOver.Pushforward.MapInversionChoice.inverts

/-- The canonical fixed-Hom inversion family supplied by source-level localization. -/
@[stacks 04WI "canonical fixed-Hom pushforward inversion family"]
theorem MapInversionChoice.canonical (u : C ⥤ D)
    (X Y : FiberedCategoryOver.{uC, vC, uS, vS} C) :
    MapInversionChoice u X Y := sorry

/-- The bundled endpoint choices and fixed-owner map-inversion family needed for pushforward on
one Hom category of fibred categories. -/
@[stacks 04WI "bundled pushforward inversion choice"]
structure InversionChoice (u : C ⥤ D)
    (X Y : FiberedCategoryOver.{uC, vC, uS, vS} C) : Prop extends
    mapChoice : MapInversionChoice u X Y where
  /-- The projection choice for the source pushforward. -/
  source : ProjectionChoice u X
  /-- The projection choice for the target pushforward. -/
  target : ProjectionChoice u Y

attribute [stacks 04WI "bundled pushforward map inversion choice field"]
  FiberedCategoryOver.Pushforward.InversionChoice.mapChoice
attribute [stacks 04WI "bundled pushforward source projection choice field"]
  FiberedCategoryOver.Pushforward.InversionChoice.source
attribute [stacks 04WI "bundled pushforward target projection choice field"]
  FiberedCategoryOver.Pushforward.InversionChoice.target

/-- The fixed-owner inversion family underlying a bundled pushforward choice. -/
add_decl_doc InversionChoice.mapChoice

set_option linter.defProp false in
/-- Add endpoint projection choices to a fixed-owner map-inversion family. -/
@[stacks 04WI "fixed-Hom pushforward inversion family with endpoints"]
def MapInversionChoice.withEndpoints {u : C ⥤ D}
    {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
    (h : MapInversionChoice u X Y)
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y) :
    InversionChoice u X Y where
  mapChoice := h
  source := hX
  target := hY

/-- The source endpoint of a fixed-owner inversion family with endpoints is the supplied source
projection choice. -/
@[simp, stacks 04WI "fixed-Hom inversion source endpoint readout"]
theorem MapInversionChoice.withEndpoints.source
    {u : C ⥤ D} {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
    (h : MapInversionChoice u X Y) (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y) :
    (MapInversionChoice.withEndpoints h hX hY).source = hX := sorry

/-- The target endpoint of a fixed-owner inversion family with endpoints is the supplied target
projection choice. -/
@[simp, stacks 04WI "fixed-Hom inversion target endpoint readout"]
theorem MapInversionChoice.withEndpoints.target
    {u : C ⥤ D} {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
    (h : MapInversionChoice u X Y) (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y) :
    (MapInversionChoice.withEndpoints h hX hY).target = hY := sorry

/-- Adding endpoint choices does not change the underlying fixed-owner inversion proof. -/
@[simp, stacks 04WI "fixed-Hom inversion proof readout"]
theorem MapInversionChoice.withEndpoints.inverts
    {u : C ⥤ D} {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
    (h : MapInversionChoice u X Y) (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : X ⟶ Y) :
    (MapInversionChoice.withEndpoints h hX hY).inverts F = h.inverts F := sorry

/-- Combine bundled endpoint projection choices with the canonical inversion theorem for every
morphism between the fixed fibred categories.  The result is proof-only; consumers that define
data may instead keep an explicit `InversionChoice` argument to isolate proof debt. -/
@[stacks 04WI "bundled pushforward inversion choice from endpoints"]
theorem InversionChoice.ofProjectionChoices {u : C ⥤ D}
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y) :
    InversionChoice u X Y := sorry

/-- Pass from a fixed-owner bundled inversion family to the cartesian Hom presentation. Every
cartesian based functor between `X.p` and `Y.p` is represented by the existing cartesian Hom
equivalence, so no extra inversion hypothesis is required. -/
@[stacks 04WI "bundled-to-cartesian pushforward inversion choice"]
theorem InversionChoice.toCartesian {u : C ⥤ D}
    {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
    (h : InversionChoice u X Y) :
    CartesianBasedFunctor.Pushforward.InversionChoice u X.p Y.p := sorry

/-- Lemma 8.12.8 (tag 04WI): the map between bundled pushforward fibered categories induced by
a morphism of fibered categories over `C`. -/
@[stacks 04WI "fixed-owner pushforward map"]
noncomputable def map (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : X ⟶ Y)
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F)) :
    FiberedCategoryOver.pushforward u X hX ⟶ FiberedCategoryOver.pushforward u Y hY :=
  (FiberedCategoryOver.CartesianHom.toHom
    (FiberedCategoryOver.pushforward u X hX)
    (FiberedCategoryOver.pushforward u Y hY)).obj
      (CartesianBasedFunctor.Pushforward.map u
        (FiberedCategoryOver.toCartesianBasedFunctor F)
        hX.raw hY.raw hF)

/-- The bundled pushforward map determined by an endpoint-and-inversion choice bundle. -/
@[stacks 04WI "bundled pushforward map from inversion choice"]
noncomputable def map.ofInversionChoice
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : X ⟶ Y) (h : InversionChoice u X Y) :
    FiberedCategoryOver.pushforward u X h.source ⟶
      FiberedCategoryOver.pushforward u Y h.target :=
  map u F h.source h.target (h.inverts F)

/-- Forgetting an explicit fixed-owner pushforward map to cartesian based functors recovers the
universe-polymorphic pushforward owner. -/
@[simp, stacks 04WI "bundled pushforward cartesian map computation"]
theorem map.toCartesianBasedFunctor
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : X ⟶ Y)
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F)) :
    FiberedCategoryOver.toCartesianBasedFunctor (map u F hX hY hF) =
      CartesianBasedFunctor.Pushforward.map u
        (FiberedCategoryOver.toCartesianBasedFunctor F)
        hX.raw hY.raw hF := sorry

/-- Lemma 8.12.8 (tag 04WI): forgetting a bundled pushforward map recovers the based functor
induced by the raw localized pushforward map. -/
@[simp, stacks 04WI "bundled pushforward based map computation"]
theorem map.toBasedFunctor (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : X ⟶ Y)
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F)) :
    FiberedCategoryOver.toBasedFunctor (map u F hX hY hF) =
      BasedFunctor.ofFunctor
        (Functor.Pushforward.map u (FiberedCategoryOver.toCartesianBasedFunctor F) hF)
        (Functor.Pushforward.map.compProjection u
          hX.raw hY.raw
          (FiberedCategoryOver.toCartesianBasedFunctor F) hF) := sorry

/-- Lemma 8.12.8 (tag 04WI): the total functor underlying a bundled pushforward map is the raw
localized pushforward map. -/
@[simp, stacks 04WI "bundled pushforward total map computation"]
theorem map.toFunctor (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : X ⟶ Y)
    (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (hF : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F)) :
    FiberedCategoryOver.toFunctor (map u F hX hY hF) =
      Functor.Pushforward.map u (FiberedCategoryOver.toCartesianBasedFunctor F) hF := sorry

end FiberedCategoryOver.Pushforward

end CategoryTheory

-- Data audit: `withEndpoints` transparently packages its three explicit inputs. `toCartesian`
-- is proposition-valued transport across the cartesian Hom presentation. The coherent owner
-- lives in the pseudofunctor coherence leaf and keeps comparison isomorphisms as explicit data.
