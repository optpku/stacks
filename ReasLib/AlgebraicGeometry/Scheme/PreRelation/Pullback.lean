/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Pullback of relations on schemes

This module defines base change of pre-relations and relations in the slice category of schemes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace PreRelation

/-- Pull a pre-relation on `U` back along a morphism `g : U' ⟶ U` over the base. -/
def pullback {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U) (g : U' ⟶ U) :
    PreRelation U' :=
  (Over.pullback (prod.map g g)).obj P

/-- The source of a pulled-back pre-relation is the categorical pullback of its source. -/
theorem pullback_left {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) :
    (P.pullback g).left = Limits.pullback P.hom (prod.map g g) := rfl

/-- The defining map of a pulled-back pre-relation is the second pullback projection. -/
theorem pullback_hom {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) :
    (P.pullback g).hom = Limits.pullback.snd P.hom (prod.map g g) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pullback relates two points exactly when their images are related by the original
pre-relation. -/
theorem pullback_pointRel_iff {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) (T : Over S) (x y : T ⟶ U') :
    (P.pullback g).pointRel T x y ↔ P.pointRel T (x ≫ g) (y ≫ g) := by
  constructor
  · rintro ⟨r, hx, hy⟩
    refine ⟨r ≫ Limits.pullback.fst _ _, ?_, ?_⟩
    · calc
        (r ≫ Limits.pullback.fst _ _) ≫ P.t =
            (r ≫ (P.pullback g).t) ≫ g := by
          simpa only [t, pullback_hom, Category.assoc, prod.map_fst] using
            congrArg (fun k ↦ r ≫ k ≫ prod.fst)
              (Limits.pullback.condition (f := P.hom) (g := prod.map g g))
        _ = x ≫ g := by rw [hx]
    · calc
        (r ≫ Limits.pullback.fst _ _) ≫ P.s =
            (r ≫ (P.pullback g).s) ≫ g := by
          simpa only [s, pullback_hom, Category.assoc, prod.map_snd] using
            congrArg (fun k ↦ r ≫ k ≫ prod.snd)
              (Limits.pullback.condition (f := P.hom) (g := prod.map g g))
        _ = y ≫ g := by rw [hy]
  · rintro ⟨r, hx, hy⟩
    have h : r ≫ P.hom = prod.lift x y ≫ prod.map g g := by
      apply prod.hom_ext
      · simpa only [t, Category.assoc, prod.map_fst, prod.lift_fst_assoc] using hx
      · simpa only [s, Category.assoc, prod.map_snd, prod.lift_snd_assoc] using hy
    refine ⟨Limits.pullback.lift r (prod.lift x y) h, ?_, ?_⟩
    · simpa only [t, pullback_hom, Category.assoc, prod.lift_fst] using
        congrArg (fun k ↦ k ≫ prod.fst) (Limits.pullback.lift_snd r (prod.lift x y) h)
    · simpa only [s, pullback_hom, Category.assoc, prod.lift_snd] using
        congrArg (fun k ↦ k ≫ prod.snd) (Limits.pullback.lift_snd r (prod.lift x y) h)

/-- Pulling back a pre-relation with monic defining map preserves monicity. -/
instance instMonoHomPullback {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) [Mono P.hom] : Mono (P.pullback g).hom := by
  change Mono (Limits.pullback.snd P.hom (prod.map g g))
  infer_instance

namespace IsPreEquivalence

/-- Pullback preserves pointwise pre-equivalence. -/
theorem pullback {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    (hP : P.IsPreEquivalence) (g : U' ⟶ U) : (P.pullback g).IsPreEquivalence := by
  intro T
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (pullback_pointRel_iff P g T x x).2 ((hP T).refl _)
  · intro x y hxy
    exact (pullback_pointRel_iff P g T y x).2
      ((hP T).symm ((pullback_pointRel_iff P g T x y).1 hxy))
  · intro x y z hxy hyz
    exact (pullback_pointRel_iff P g T x z).2
      ((hP T).trans ((pullback_pointRel_iff P g T x y).1 hxy)
        ((pullback_pointRel_iff P g T y z).1 hyz))

end IsPreEquivalence

/-- Pullback preserves internal equivalence relations. -/
instance instIsEquivalenceRelationPullback {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s] :
    IsEquivalenceRelation (P.pullback g).t (P.pullback g).s := by
  obtain ⟨e⟩ := IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := P.t) (p₂ := P.s)
  haveI : Mono P.hom := ⟨fun a b h ↦ e.right_cancellation a b
    (by simpa only [t, Category.assoc] using congrArg (fun k ↦ k ≫ prod.fst) h)
    (by simpa only [s, Category.assoc] using congrArg (fun k ↦ k ≫ prod.snd) h)⟩
  have hP : P.IsPreEquivalence := by
    intro T
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨x ≫ e.r, by simp, by simp⟩
    · rintro x y ⟨r, hx, hy⟩
      exact ⟨r ≫ e.s, by simpa only [Category.assoc, e.symmetry₁] using hy,
        by simpa only [Category.assoc, e.symmetry₂] using hx⟩
    · rintro x y z ⟨r, hx, hy⟩ ⟨r', hy', hz⟩
      let l := PullbackCone.IsLimit.lift e.isLimit r r' (hy.trans hy'.symm)
      exact ⟨l ≫ e.t,
        by simpa only [Category.assoc, e.transitivity₁, l,
          PullbackCone.IsLimit.lift_fst_assoc] using hx,
        by simpa only [Category.assoc, e.transitivity₂, l,
          PullbackCone.IsLimit.lift_snd_assoc] using hz⟩
  let R := P.pullback g
  haveI : Mono R.hom := instMonoHomPullback P g
  have hR : R.IsPreEquivalence := hP.pullback g
  obtain ⟨r, hr₁, hr₂⟩ := (hR U').refl (𝟙 U')
  have hi : R.pointRel R.left R.s R.t :=
    (hR R.left).symm ⟨𝟙 _, by simp, by simp⟩
  obtain ⟨i, hi₁, hi₂⟩ := hi
  have hc₁ : R.pointRel (Limits.pullback R.s R.t)
      (Limits.pullback.fst R.s R.t ≫ R.t)
      (Limits.pullback.fst R.s R.t ≫ R.s) :=
    ⟨Limits.pullback.fst _ _, rfl, rfl⟩
  have hc₂ : R.pointRel (Limits.pullback R.s R.t)
      (Limits.pullback.fst R.s R.t ≫ R.s)
      (Limits.pullback.snd R.s R.t ≫ R.s) :=
    ⟨Limits.pullback.snd _ _, Limits.pullback.condition.symm, rfl⟩
  obtain ⟨c, hc₁, hc₂⟩ := (hR _).trans hc₁ hc₂
  exact ⟨⟨{
    right_cancellation := fun _ a b h₁ h₂ ↦ (cancel_mono R.hom).1 (prod.hom_ext
      (by simpa only [t, Category.assoc] using h₁)
      (by simpa only [s, Category.assoc] using h₂))
    r := r
    reflexivity₁ := hr₁
    reflexivity₂ := hr₂
    s := i
    symmetry₁ := hi₁
    symmetry₂ := hi₂
    c := Limits.pullback.cone R.s R.t
    isLimit := Limits.pullback.isLimit R.s R.t
    t := c
    transitivity₁ := hc₁
    transitivity₂ := hc₂ }⟩⟩

end PreRelation

namespace Relation

/-- Pull a relation on `U` back along a morphism `g : U' ⟶ U` over the base. -/
def pullback {S : Scheme.{u}} {U U' : Over S} (Q : Relation U) (g : U' ⟶ U) :
    Relation U' :=
  (MonoOver.pullback (prod.map g g)).obj Q

/-- Forgetting monicity after pulling back a relation gives the pulled-back pre-relation. -/
theorem pullback_toPreRelation {S : Scheme.{u}} {U U' : Over S} (Q : Relation U)
    (g : U' ⟶ U) :
    (Q.pullback g).toPreRelation = Q.toPreRelation.pullback g := rfl

end Relation

end AlgebraicGeometry.Scheme
