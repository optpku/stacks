/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Precompose
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.Fibered
public import ReasLib.CategoryTheory.Fibered.Pushforward.Unit.Naturality.Map

/-!
# Source naturality of pushforward-unit precomposition

This file constructs the source-variable comparison at the neutral based-functor level. Its
objectwise data come from the canonical localization comparison for the pushforward map.
-/

@[expose] public section

universe uC uD uS uT uZ vC vD vS vT vZ

namespace CategoryTheory

open Limits
open scoped BasedFunctor Functor

namespace FiberedCategoryOver.Pushforward.Precompose.Source

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

variable {X : FiberedCategoryOver.{uC, vC, uS, vS} C}
variable {Y : FiberedCategoryOver.{uC, vC, uT, vT} C}
variable {Z : FiberedCategoryOver.{uD, vD, uZ, vZ} D}

/-- The pullback compatibility for the objectwise source comparison of pushforward-unit
precomposition. -/
@[stacks 04WI "source naturality pullback compatibility"]
theorem app.w (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    u.map (F.toBasedFunctor.projectionIso.app x).inv ≫
        ((F.toBasedFunctor ⋙ Precompose.obj (hX := hY) u G).obj x).iso.hom =
      (Precompose.obj (hX := hX) u
          ((CartesianBasedFunctor.Pushforward.map u F hX.raw hY.raw hF).toBasedFunctor ⋙ G)
        |>.obj x).iso.hom ≫
        Z.p.map (G.toFunctor.map
          (Functor.Pushforward.Unit.mapIsoApp u F hF x).hom) := sorry

/-- The objectwise source comparison for pushforward-unit precomposition. Its pullback
components are the based projection comparison of `F` and the image under `G` of the canonical
pushforward-unit comparison. -/
@[stacks 04WI "source naturality pullback component"]
noncomputable def app (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (Precompose.obj (hX := hX) u
        ((CartesianBasedFunctor.Pushforward.map u F hX.raw hY.raw hF).toBasedFunctor ⋙ G)).obj x ≅
      (F.toBasedFunctor ⋙ Precompose.obj (hX := hY) u G).obj x :=
  CategoricalPullback.mkIso
    (F.toBasedFunctor.projectionIso.app x).symm
    (G.toFunctor.mapIso (Functor.Pushforward.Unit.mapIsoApp u F hF x))
    (app.w u hX hY F hF G x)

/-- The first forward pullback component of the objectwise source comparison. -/
@[simp, stacks 04WI "source naturality forward first component"]
theorem app.hom.fst (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (app u hX hY F hF G x).hom.fst =
      (F.toBasedFunctor.projectionIso.app x).inv := sorry

/-- The second forward pullback component of the objectwise source comparison is the image of
the canonical pushforward-unit comparison. -/
@[simp, stacks 04WI "source naturality forward second component"]
theorem app.hom.snd (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (app u hX hY F hF G x).hom.snd =
      G.toFunctor.map (Functor.Pushforward.Unit.mapIsoApp u F hF x).hom := sorry

/-- The first inverse pullback component of the objectwise source comparison. -/
@[simp, stacks 04WI "source naturality inverse first component"]
theorem app.inv.fst (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (app u hX hY F hF G x).inv.fst =
      (F.toBasedFunctor.projectionIso.app x).hom := sorry

/-- The second inverse pullback component of the objectwise source comparison is the image of
the inverse canonical pushforward-unit comparison. -/
@[simp, stacks 04WI "source naturality inverse second component"]
theorem app.inv.snd (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (app u hX hY F hF G x).inv.snd =
      G.toFunctor.map (Functor.Pushforward.Unit.mapIsoApp u F hF x).inv := sorry

/-- The second forward pullback component, expanded into the localization comparison and the
prelocalized unit-object comparison. -/
@[stacks 04WI "source naturality forward comparison expansion"]
theorem app.hom.snd_comparison (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (app u hX hY F hF G x).hom.snd =
      G.toFunctor.map
        ((Functor.Pushforward.map.comparisonIso u F hF).hom.app
            (Functor.Pushforward.Prelocalized.obj u X.p x) ≫
          (u.pushforwardFractions Y.p).Q.map
            (Functor.Pushforward.Prelocalized.mapObjIso u F x).hom) := sorry

/-- The second inverse pullback component, expanded into the prelocalized unit-object
comparison and the inverse localization comparison. -/
@[stacks 04WI "source naturality inverse comparison expansion"]
theorem app.inv.snd_comparison (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (app u hX hY F hF G x).inv.snd =
      G.toFunctor.map
        ((u.pushforwardFractions Y.p).Q.map
            (Functor.Pushforward.Prelocalized.mapObjIso u F x).inv ≫
          (Functor.Pushforward.map.comparisonIso u F hF).inv.app
            (Functor.Pushforward.Prelocalized.obj u X.p x)) := sorry

/-- The objectwise source comparison is natural in the total source object. -/
@[stacks 04WI "source naturality component naturality"]
theorem app.naturality (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    {x y : X.total} (f : x ⟶ y) :
    (Precompose.obj (hX := hX) u
        ((CartesianBasedFunctor.Pushforward.map u F hX.raw hY.raw hF).toBasedFunctor ⋙ G)).map f ≫
        (app u hX hY F hF G y).hom =
      (app u hX hY F hF G x).hom ≫
        (F.toBasedFunctor ⋙ Precompose.obj (hX := hY) u G).map f := sorry

/-- Every forward source-comparison component lies over the identity of its source base
object. -/
@[stacks 04WI "source naturality component lift"]
theorem app.isHomLift (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (FiberedCategoryOver.pullback u Z).p.IsHomLift
      (𝟙 (X.p.obj x)) (app u hX hY F hF G x).hom := sorry

/-- The source-variable natural isomorphism for pushforward-unit precomposition, at the neutral
based-functor level. -/
@[stacks 04WI "source naturality based isomorphism"]
noncomputable def iso (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory) :
    Precompose.obj (hX := hX) u
        ((CartesianBasedFunctor.Pushforward.map u F hX.raw hY.raw hF).toBasedFunctor ⋙ G) ≅
      F.toBasedFunctor ⋙ Precompose.obj (hX := hY) u G :=
  BasedNatIso.ofComponents (app u hX hY F hF G)
    (app.naturality u hX hY F hF G) (app.isHomLift u hX hY F hF G)

/-- The forward component of the source-variable natural isomorphism is the explicit pullback
comparison component. -/
@[simp, stacks 04WI "source naturality isomorphism forward component"]
theorem iso.hom.app (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (iso u hX hY F hF G).hom.toNatTrans.app x = (app u hX hY F hF G x).hom := sorry

/-- The inverse component of the source-variable natural isomorphism is the inverse explicit
pullback comparison component. -/
@[simp, stacks 04WI "source naturality isomorphism inverse component"]
theorem iso.inv.app (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    (iso u hX hY F hF G).inv.toNatTrans.app x = (app u hX hY F hF G x).inv := sorry

/-- The first forward pullback component of the source-variable natural isomorphism. -/
@[simp, stacks 04WI "source naturality isomorphism forward first component"]
theorem iso.hom.app.fst (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    ((iso u hX hY F hF G).hom.toNatTrans.app x).fst =
      (F.toBasedFunctor.projectionIso.app x).inv := sorry

/-- The second forward pullback component of the source-variable natural isomorphism. -/
@[simp, stacks 04WI "source naturality isomorphism forward second component"]
theorem iso.hom.app.snd (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    ((iso u hX hY F hF G).hom.toNatTrans.app x).snd =
      G.toFunctor.map (Functor.Pushforward.Unit.mapIsoApp u F hF x).hom := sorry

/-- The first inverse pullback component of the source-variable natural isomorphism. -/
@[simp, stacks 04WI "source naturality isomorphism inverse first component"]
theorem iso.inv.app.fst (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    ((iso u hX hY F hF G).inv.toNatTrans.app x).fst =
      (F.toBasedFunctor.projectionIso.app x).hom := sorry

/-- The second inverse pullback component of the source-variable natural isomorphism. -/
@[simp, stacks 04WI "source naturality isomorphism inverse second component"]
theorem iso.inv.app.snd (hX : ProjectionChoice u X) (hY : ProjectionChoice u Y)
    (F : CartesianBasedFunctor X.p Y.p)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (G : (FiberedCategoryOver.pushforward u Y hY).toBasedCategory ⥤ᵇ Z.toBasedCategory)
    (x : X.total) :
    ((iso u hX hY F hF G).inv.toNatTrans.app x).snd =
      G.toFunctor.map (Functor.Pushforward.Unit.mapIsoApp u F hF x).inv := sorry

end FiberedCategoryOver.Pushforward.Precompose.Source

end CategoryTheory

-- Data audit: `Source.app` owns explicit pullback-isomorphism data. Its `sorryAx` dependency and
-- that of `Source.iso` are confined to compatibility, naturality, and verticality laws.
