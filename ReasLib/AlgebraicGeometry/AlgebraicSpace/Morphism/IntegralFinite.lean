/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Affine tests for representable integral and finite morphisms

A representable morphism of algebraic spaces is integral, respectively finite,
if and only if every base change along an affine scheme is an affine scheme
integral, respectively finite, over that scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine-scheme test for a representable morphism `f` to be integral:
every base change of `f` along a morphism from an affine scheme `Z` is an
affine scheme integral over `Z`. -/
def affineAndIntegralOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) : Prop :=
  ∀ {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints),
    IsAffine Z.left →
      IsAffine (hf.pullback g).left ∧ IsIntegralHom (hf.snd g).left

namespace affineAndIntegralOnAffineSchemes

/-- The affine-scheme integral test applies to a given morphism from an affine
scheme. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndIntegralOnAffineSchemes hf) {Z : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints) (hZ : IsAffine Z.left) :
    IsAffine (hf.pullback g).left ∧ IsIntegralHom (hf.snd g).left :=
  h g hZ

/-- The affine-scheme integral test holds for every represented pullback square,
not only for the chosen `hf.pullback`. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndIntegralOnAffineSchemes hf) {Z W : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hZ : IsAffine Z.left) (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ IsIntegralHom snd.left := by
  let e := yoneda.preimageIso (hpb.isoIsPullback _ _ (hf.isPullback g))
  have he : e.hom ≫ hf.snd g = snd := by
    apply yoneda.map_injective
    simp [e]
  have he' : e.hom.left ≫ (hf.snd g).left = snd.left :=
    congrArg (fun k : W ⟶ Z ↦ k.left) he
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  haveI : IsIntegralHom (hf.snd g).left := (h g hZ).2
  haveI : IsIntegralHom snd.left := by
    rw [← he']
    infer_instance
  letI := hZ
  exact ⟨isAffine_of_isAffineHom snd.left, inferInstance⟩

end affineAndIntegralOnAffineSchemes

/-- The affine-scheme test for a representable morphism `f` to be finite: every
base change of `f` along a morphism from an affine scheme `Z` is an affine
scheme finite over `Z`. -/
def affineAndFiniteOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) : Prop :=
  ∀ {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints),
    IsAffine Z.left → IsAffine (hf.pullback g).left ∧ IsFinite (hf.snd g).left

namespace affineAndFiniteOnAffineSchemes

/-- The affine-scheme finite test applies to a given morphism from an affine
scheme. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndFiniteOnAffineSchemes hf) {Z : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints) (hZ : IsAffine Z.left) :
    IsAffine (hf.pullback g).left ∧ IsFinite (hf.snd g).left :=
  h g hZ

/-- The affine-scheme finite test holds for every represented pullback square,
not only for the chosen `hf.pullback`. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndFiniteOnAffineSchemes hf) {Z W : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hZ : IsAffine Z.left) (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ IsFinite snd.left := by
  let e := yoneda.preimageIso (hpb.isoIsPullback _ _ (hf.isPullback g))
  have he : e.hom ≫ hf.snd g = snd := by
    apply yoneda.map_injective
    simp [e]
  have he' : e.hom.left ≫ (hf.snd g).left = snd.left :=
    congrArg (fun k : W ⟶ Z ↦ k.left) he
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  haveI : IsFinite (hf.snd g).left := (h g hZ).2
  haveI : IsFinite snd.left := by
    rw [← he']
    infer_instance
  letI := hZ
  exact ⟨isAffine_of_isAffineHom snd.left, inferInstance⟩

end affineAndFiniteOnAffineSchemes

/-- A representable morphism of algebraic spaces is integral if and only if
every affine scheme base change is affine and integral over the base. -/
theorem integralHom_presheaf_iff_affineAndIntegralOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f ↔
      affineAndIntegralOnAffineSchemes hf := by
  constructor
  · intro h Z g hZ
    haveI : IsIntegralHom (hf.snd g).left := h.property g _ _ (hf.isPullback g)
    letI := hZ
    exact ⟨isAffine_of_isAffineHom (hf.snd g).left, inferInstance⟩
  · intro h
    refine ⟨hf, ?_⟩
    intro Z W g fst snd hpb
    change IsIntegralHom snd.left
    apply IsZariskiLocalAtTarget.of_openCover Z.left.affineCover
    intro i
    let Zi : Over S := Over.mk (Z.left.affineCover.f i ≫ Z.hom)
    let ι : Zi ⟶ Z := Over.homMk (Z.left.affineCover.f i)
    let Wi : Over S := Over.mk
      (pullback.fst snd.left (Z.left.affineCover.f i) ≫ W.hom)
    let p : Wi ⟶ W := Over.homMk (pullback.fst _ _)
    let q : Wi ⟶ Zi := Over.homMk (pullback.snd _ _) (by
      change pullback.snd snd.left (Z.left.affineCover.f i) ≫
          (Z.left.affineCover.f i ≫ Z.hom) =
        pullback.fst snd.left (Z.left.affineCover.f i) ≫ W.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w snd])
    have hpq : IsPullback p q snd ι :=
      IsPullback.of_map (Over.forget S) (by ext; exact pullback.condition)
        (IsPullback.of_hasPullback _ _)
    exact (h.of_isPullback (yoneda.map ι ≫ g) (yoneda.map p ≫ fst) q
      (by change IsAffine (Z.left.affineCover.X i); infer_instance)
      ((hpq.map yoneda).paste_horiz hpb)).2

/-- A representable morphism that is integral satisfies the affine-scheme integral test. -/
theorem affineAndIntegralOnAffineSchemes_of_integralHom_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f) :
    affineAndIntegralOnAffineSchemes hf :=
  (integralHom_presheaf_iff_affineAndIntegralOnAffineSchemes hf).mp h

/-- A representable morphism that satisfies the affine-scheme integral test is
integral. -/
theorem integralHom_presheaf_of_affineAndIntegralOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : affineAndIntegralOnAffineSchemes hf) :
    (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f :=
  (integralHom_presheaf_iff_affineAndIntegralOnAffineSchemes hf).mpr h

/-- A representable morphism of algebraic spaces is finite if and only if
every affine scheme base change is affine and finite over the base. -/
theorem finite_presheaf_iff_affineAndFiniteOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f ↔
      affineAndFiniteOnAffineSchemes hf := by
  constructor
  · intro h Z g hZ
    haveI : IsFinite (hf.snd g).left := h.property g _ _ (hf.isPullback g)
    letI := hZ
    exact ⟨isAffine_of_isAffineHom (hf.snd g).left, inferInstance⟩
  · intro h
    refine ⟨hf, ?_⟩
    intro Z W g fst snd hpb
    change IsFinite snd.left
    apply IsZariskiLocalAtTarget.of_openCover Z.left.affineCover
    intro i
    let Zi : Over S := Over.mk (Z.left.affineCover.f i ≫ Z.hom)
    let ι : Zi ⟶ Z := Over.homMk (Z.left.affineCover.f i)
    let Wi : Over S := Over.mk
      (pullback.fst snd.left (Z.left.affineCover.f i) ≫ W.hom)
    let p : Wi ⟶ W := Over.homMk (pullback.fst _ _)
    let q : Wi ⟶ Zi := Over.homMk (pullback.snd _ _) (by
      change pullback.snd snd.left (Z.left.affineCover.f i) ≫
          (Z.left.affineCover.f i ≫ Z.hom) =
        pullback.fst snd.left (Z.left.affineCover.f i) ≫ W.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w snd])
    have hpq : IsPullback p q snd ι :=
      IsPullback.of_map (Over.forget S) (by ext; exact pullback.condition)
        (IsPullback.of_hasPullback _ _)
    exact (h.of_isPullback (yoneda.map ι ≫ g) (yoneda.map p ≫ fst) q
      (by change IsAffine (Z.left.affineCover.X i); infer_instance)
      ((hpq.map yoneda).paste_horiz hpb)).2

/-- A representable morphism that is finite satisfies the affine-scheme finite test. -/
theorem affineAndFiniteOnAffineSchemes_of_finite_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f) :
    affineAndFiniteOnAffineSchemes hf :=
  (finite_presheaf_iff_affineAndFiniteOnAffineSchemes hf).mp h

/-- A representable morphism that satisfies the affine-scheme finite test is
finite. -/
theorem finite_presheaf_of_affineAndFiniteOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : affineAndFiniteOnAffineSchemes hf) :
    (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f :=
  (finite_presheaf_iff_affineAndFiniteOnAffineSchemes hf).mpr h

end AlgebraicGeometry.AlgebraicSpace
