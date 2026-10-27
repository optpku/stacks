/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward of categories fibred in groupoids

The localized pushforward of a category fibred in groupoids is again fibred in groupoids under
the finite-limit hypotheses used to construct the pushforward projection.  This is independent
of any topology or stack condition.

## Main declarations

* `Functor.Pushforward.projectionInGroupoids` — the projection-level preservation
  theorem.
* `FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice` — explicit projection
  certification at the groupoid-fibred layer.
* `FiberedCategoryOver.Groupoids.pushforward` — the bundled pushforward construction.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

namespace Functor

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Lemma 8.12.7 (tag 04WH): an explicitly chosen localized pushforward projection of a
category fibred in groupoids is again fibred in groupoids. -/
@[stacks 04WH]
theorem Pushforward.projectionInGroupoids
    (u : C ⥤ D) (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Pushforward.ProjectionChoice u p) :
    Functor.IsFibered.InGroupoids (u.pushforwardProjection p h) := by
  let W := u.pushforwardFractions p
  let Q := W.Q
  let q := u.pushforwardProjection p h
  have map_Q {X Y : u.pushforwardSource p} (f : X ⟶ Y) :
      q.map (Q.map f) = (Pushforward.sourceProjection u p).map f := by
    have hcomp : Q ⋙ q = Pushforward.sourceProjection u p :=
      Localization.Construction.fac _ h.inverts
    have hmap := Functor.congr_hom hcomp f
    change q.map (Q.map f) =
      𝟙 ((Pushforward.sourceProjection u p).obj X) ≫
        (Pushforward.sourceProjection u p).map f ≫
          𝟙 ((Pushforward.sourceProjection u p).obj Y) at hmap
    simpa only [Category.id_comp, Category.comp_id] using hmap
  -- A vertical right fraction has a vertical numerator, so both parts are inverted.
  have vertical_isIso : ∀ {X Y : u.pushforward p} {V : D} (f : X ⟶ Y),
      q.IsHomLift (𝟙 V) f → IsIso f := by
    intro X Y V f hf
    obtain ⟨X, rfl⟩ := (Localization.Construction.objEquiv W).surjective X
    obtain ⟨Y, rfl⟩ := (Localization.Construction.objEquiv W).surjective Y
    obtain ⟨a, rfl⟩ := Localization.exists_rightFraction Q W f
    obtain ⟨U, hU⟩ := a.hs.1
    letI hs_source : (Pushforward.sourceProjection u p).IsHomLift (𝟙 U) a.s := hU
    letI hf_lift : q.IsHomLift (𝟙 V) (a.map Q (Localization.inverts Q W)) := hf
    have hs_dom := @IsHomLift.domain_eq _ _ _ _ (Pushforward.sourceProjection u p)
      _ _ _ _ (𝟙 U) a.s hs_source
    have hs_cod := @IsHomLift.codomain_eq _ _ _ _ (Pushforward.sourceProjection u p)
      _ _ _ _ (𝟙 U) a.s hs_source
    haveI hs_lift : q.IsHomLift (𝟙 U) (Q.map a.s) :=
      IsHomLift.of_fac' q (𝟙 U) (Q.map a.s) hs_dom hs_cod
        (by
          rw [map_Q]
          exact IsHomLift.fac' (Pushforward.sourceProjection u p) (𝟙 U) a.s)
    have hnum_lift := IsHomLift.comp_lift_id_left' q U (Q.map a.s) (𝟙 V)
      (a.map Q (Localization.inverts Q W))
    rw [a.map_s_comp_map] at hnum_lift
    have hnum : W a.f := by
      refine ⟨⟨V, ?_⟩, ?_⟩
      · letI hnum_lift' := hnum_lift
        exact IsHomLift.of_fac' (Pushforward.sourceProjection u p) (𝟙 V) a.f
          (IsHomLift.domain_eq q (𝟙 V) (Q.map a.f))
          (IsHomLift.codomain_eq q (𝟙 V) (Q.map a.f))
          (by
            rw [← map_Q]
            exact IsHomLift.fac' q (𝟙 V) (Q.map a.f))
      · change p.IsStronglyCartesian (p.map a.f.snd) a.f.snd
        infer_instance
    haveI hf_iso : IsIso (Q.map a.f) := Localization.inverts Q W a.f hnum
    haveI hs_iso : IsIso (Q.map a.s) := Localization.inverts Q W a.s a.hs
    change IsIso (CategoryTheory.inv (Q.map a.s) ≫ Q.map a.f)
    exact IsIso.comp_isIso'
      (@IsIso.inv_isIso _ _ _ _ (Q.map a.s) hs_iso) hf_iso
  letI : q.IsFibered := Pushforward.projectionIsFibered u p h
  refine { toIsFibered := inferInstance, all_isCartesian := ?_ }
  intro X Y f
  -- Compare an arbitrary arrow with a Cartesian lift of its image.
  obtain ⟨Z, g, hg⟩ := IsPreFibered.exists_isCartesian q (a := Y) rfl (q.map f)
  letI hg_cartesian := hg
  let k := IsCartesian.map q (q.map f) g f
  letI hk_lift : q.IsHomLift (𝟙 (q.obj X)) k := IsCartesian.map_isHomLift q (q.map f) g f
  letI hk_iso : IsIso k := vertical_isIso k hk_lift
  have hc : q.IsCartesian (q.map f) (k ≫ g) :=
    @IsCartesian.of_iso_comp _ _ _ _ q _ _ _ _ (q.map f) g hg _ (asIso k) hk_lift
  simpa only [k, IsCartesian.fac] using hc

end Functor

namespace FiberedCategoryOver.Groupoids

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace Pushforward

/-- The explicit projection choice needed to bundle a localized pushforward as a category
fibred in groupoids. -/
@[stacks 04WH]
structure ProjectionChoice (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C) : Prop where
  /-- The prelocalized projection inverts the pushforward fractions. -/
  inverts : (u.pushforwardFractions X.p).IsInvertedBy
    (Functor.Pushforward.sourceProjection u X.p)
  /-- The explicitly induced projection is fibred in groupoids. -/
  inGroupoids : Functor.IsFibered.InGroupoids
    (Functor.Pushforward.projection u X.p inverts)

/-- The canonical groupoid-fibred projection choice obtained from the localization construction
under the standard finite-limit hypotheses.
-/
@[stacks 04WH "canonical groupoid-fibred pushforward choice"]
theorem ProjectionChoice.canonical (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    ProjectionChoice u X := by
  let h : Functor.Pushforward.ProjectionChoice u X.p :=
    ⟨by
      intro Y Z f hf
      obtain ⟨V, hV⟩ := hf.1
      letI := hV
      rw [IsHomLift.fac' (Functor.Pushforward.sourceProjection u X.p) (𝟙 V) f]
      infer_instance⟩
  exact ⟨h.inverts, Functor.Pushforward.projectionInGroupoids u X.p h⟩

/-- Forget a groupoid-fibred projection choice to its raw fraction-inversion component. -/
@[stacks 04WH "groupoid-fibred pushforward raw choice"]
theorem ProjectionChoice.raw {u : C ⥤ D} {X : FiberedCategoryOver.Groupoids C}
    (h : ProjectionChoice u X) : Functor.Pushforward.ProjectionChoice u X.p :=
  ⟨h.inverts⟩

/-- Forget a groupoid-fibred projection choice to the ordinary fibred-category choice on the
same underlying projection. -/
@[stacks 04WH "groupoid-fibred pushforward ordinary choice"]
theorem ProjectionChoice.toFibered {u : C ⥤ D} {X : FiberedCategoryOver.Groupoids C}
    (h : ProjectionChoice u X) :
    FiberedCategoryOver.Pushforward.ProjectionChoice u
      ((FiberedCategoryOver.Groupoids.toFibered C).obj X) :=
  ⟨h.inverts, h.inGroupoids.toIsFibered⟩

/-- Enrich a raw pushforward projection choice with an explicitly supplied proof that the
selected projection is fibred in groupoids. -/
@[stacks 04WH "groupoid-fibred pushforward choice from raw data"]
theorem ProjectionChoice.ofRawWith {u : C ⥤ D} (X : FiberedCategoryOver.Groupoids C)
    (h : Functor.Pushforward.ProjectionChoice u X.p)
    (h_groupoids : Functor.IsFibered.InGroupoids (u.pushforwardProjection X.p h)) :
    ProjectionChoice u X :=
  ⟨h.inverts, h_groupoids⟩

/-- Enrich a raw pushforward projection choice using the canonical groupoid-fibredness theorem
for the localized projection under the finite-limit hypotheses. -/
@[stacks 04WH "canonical groupoid-fibred pushforward choice from raw data"]
theorem ProjectionChoice.ofRaw {u : C ⥤ D} (X : FiberedCategoryOver.Groupoids C)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Functor.Pushforward.ProjectionChoice u X.p) : ProjectionChoice u X :=
  .ofRawWith X h (Functor.Pushforward.projectionInGroupoids u X.p h)

end Pushforward

/-- Lemma 8.12.7 (tag 04WH): the bundled pushforward of a category fibred in groupoids formed
from an explicit projection choice. -/
@[stacks 04WH "bundled groupoid-fibred pushforward"]
noncomputable def pushforward (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    FiberedCategoryOver.Groupoids D :=
  ⟨BasedCategory.ofFunctor (Functor.Pushforward.projection u X.p h.inverts), h.inGroupoids⟩

/- Axiom audit: the total category and projection are the explicit localization lifting determined
by `h.inverts`; `h.inGroupoids` contributes only the Prop-valued object-membership field. -/

/-- The total category of a bundled groupoid-fibred pushforward is the localization at the
pushforward fractions. -/
@[simp, stacks 04WH "groupoid-fibred pushforward total computation"]
theorem pushforward.total (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    (pushforward u X h).total = Functor.pushforward u X.p := rfl

/-- Lemma 8.12.7 (tag 04WH): the projection of the bundled groupoid-fibred pushforward is the
localized projection selected by the explicit choice. -/
@[simp, stacks 04WH "groupoid-fibred pushforward projection computation"]
theorem pushforward.p (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    (pushforward u X h).p = Functor.Pushforward.projection u X.p h.inverts := rfl

/-- Forgetting the groupoid-fibre refinement of a pushforward recovers the ordinary bundled
pushforward formed from the same projection choice. -/
@[simp, stacks 04WH "groupoid-fibred pushforward ordinary computation"]
theorem pushforward.toFibered (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    (FiberedCategoryOver.Groupoids.toFibered D).obj (pushforward u X h) =
      FiberedCategoryOver.pushforward u
        ((FiberedCategoryOver.Groupoids.toFibered C).obj X) h.toFibered := rfl

end FiberedCategoryOver.Groupoids

end CategoryTheory

-- Expected audit: `ProjectionChoice` is Prop-valued, while its constructor theorems carry only
-- proof debt. The bundled `pushforward` uses only the explicitly supplied projection and
-- groupoid-fibredness fields.
