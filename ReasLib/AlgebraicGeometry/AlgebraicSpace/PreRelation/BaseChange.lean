/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.CategoricalQuotient
public import ReasLib.CategoryTheory.Limits.Shapes.Cofork.BaseChange

/-!
# Base change of pre-relations

This module records the base change of an invariant pre-relation along a morphism of
targets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

-- Use the proved slice-product instance, as in the definition of `PreRelation`.
attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The base change of an invariant morphism `φ : U ⟶ X` along `f : X' ⟶ X` is the
pre-relation `j'` on `pullback φ f` whose projections are the base-changed parallel arrows
of the cofork associated to `φ`. -/
def baseChange {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    PreRelation (pullback φ f) :=
  ofHom (prod.lift
    ((P.cofork hφ).baseChangeLeft f)
    ((P.cofork hφ).baseChangeRight f))

/-- The first projection of a base-changed pre-relation is the left base-changed parallel arrow. -/
theorem baseChange_t {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).t = (P.cofork hφ).baseChangeLeft f := by
  exact prod.lift_fst _ _

/-- The second projection of a base-changed pre-relation is the right base-changed parallel arrow. -/
theorem baseChange_s {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).s = (P.cofork hφ).baseChangeRight f := by
  exact prod.lift_snd _ _

/-- The defining map of a base-changed pre-relation is the product lift of its parallel arrows. -/
theorem baseChange_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).hom =
      prod.lift
        ((P.cofork hφ).baseChangeLeft f)
        ((P.cofork hφ).baseChangeRight f) := rfl

/-- The arrow space of a base-changed pre-relation is the pullback of the original
relation arrow space along the target morphism. -/
theorem baseChange_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).left = pullback (P.t ≫ φ) f := rfl

-- Allow the definitionally equal cofork leg and `φ` in pullback comparisons.
set_option backward.isDefEq.respectTransparency false

private theorem baseChange_t_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).t ≫ pullback.fst φ f =
      pullback.fst (P.t ≫ φ) f ≫ P.t := by
  rw [baseChange_t]
  exact pullback.lift_fst _ _ _

private theorem baseChange_t_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).t ≫ pullback.snd φ f =
      pullback.snd (P.t ≫ φ) f := by
  rw [baseChange_t]
  simp only [Cofork.baseChangeLeft, cofork, Cofork.π_ofπ, pullback.map,
    pullback.lift_snd, Category.comp_id]

private theorem baseChange_s_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).s ≫ pullback.fst φ f =
      pullback.fst (P.t ≫ φ) f ≫ P.s := by
  rw [baseChange_s]
  exact pullback.lift_fst _ _ _

private theorem baseChange_s_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).s ≫ pullback.snd φ f =
      pullback.snd (P.t ≫ φ) f := by
  rw [baseChange_s]
  simp only [Cofork.baseChangeRight, cofork, Cofork.π_ofπ, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- Base change preserves the monomorphism condition on the defining map of a relation. -/
theorem monoHom_baseChange {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) [Mono P.hom] : Mono (P.baseChange hφ f).hom := by
  constructor
  intro T a b hab
  have ht : a ≫ (P.baseChange hφ f).t = b ≫ (P.baseChange hφ f).t := by
    simpa only [t, Category.assoc] using congrArg (fun k => k ≫ prod.fst) hab
  have hs : a ≫ (P.baseChange hφ f).s = b ≫ (P.baseChange hφ f).s := by
    simpa only [s, Category.assoc] using congrArg (fun k => k ≫ prod.snd) hab
  apply pullback.hom_ext (f := P.t ≫ φ) (g := f)
  · apply (instJointlyMono₂ P).right_cancellation
    · simpa only [Category.assoc, baseChange_t_fst] using
        congrArg (fun k => k ≫ pullback.fst φ f) ht
    · simpa only [Category.assoc, baseChange_s_fst] using
        congrArg (fun k => k ≫ pullback.fst φ f) hs
  · simpa only [Category.assoc, baseChange_t_snd] using
      congrArg (fun k => k ≫ pullback.snd φ f) ht

/-- On points, invariant base change retains the original relation and equality of
its two coordinates in the new target. -/
private theorem baseChange_pointRel_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) (T : Over B)
    (x y : T ⟶ pullback φ f) :
    (P.baseChange hφ f).pointRel T x y ↔
      P.pointRel T (x ≫ pullback.fst φ f) (y ≫ pullback.fst φ f) ∧
        x ≫ pullback.snd φ f = y ≫ pullback.snd φ f := by
  constructor
  · rintro ⟨r, hrx, hry⟩
    refine ⟨⟨r ≫ pullback.fst (P.t ≫ φ) f, ?_, ?_⟩, ?_⟩
    · simpa only [Category.assoc, baseChange_t_fst] using
        congrArg (fun k => k ≫ pullback.fst φ f) hrx
    · simpa only [Category.assoc, baseChange_s_fst] using
        congrArg (fun k => k ≫ pullback.fst φ f) hry
    · rw [← hrx, ← hry, Category.assoc, Category.assoc,
        baseChange_t_snd, baseChange_s_snd]
  · rintro ⟨⟨r, hrx, hry⟩, heq⟩
    have hw : r ≫ (P.t ≫ φ) = (x ≫ pullback.snd φ f) ≫ f := by
      rw [← Category.assoc, hrx, Category.assoc, pullback.condition, ← Category.assoc]
    refine ⟨pullback.lift (f := P.t ≫ φ) (g := f) r
      (x ≫ pullback.snd φ f) hw, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [Category.assoc, baseChange_t_fst, pullback.lift_fst_assoc, hrx]
      · simp only [Category.assoc, baseChange_t_snd, pullback.lift_snd]
    · apply pullback.hom_ext
      · simp only [Category.assoc, baseChange_s_fst, pullback.lift_fst_assoc, hry]
      · simpa only [Category.assoc, baseChange_s_snd, pullback.lift_snd] using heq

namespace IsPreEquivalence

/-- Base change preserves pointwise pre-equivalence of a pre-relation. -/
theorem baseChange {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    {P : PreRelation U} (hP : P.IsPreEquivalence) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).IsPreEquivalence := by
  intro T σ
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (baseChange_pointRel_iff P hφ f _ x x).mpr
      ⟨(hP T σ).refl _, rfl⟩
  · intro x y hxy
    obtain ⟨hxy, heq⟩ := (baseChange_pointRel_iff P hφ f _ x y).mp hxy
    exact (baseChange_pointRel_iff P hφ f _ y x).mpr
      ⟨(hP T σ).symm hxy, heq.symm⟩
  · intro x y z hxy hyz
    obtain ⟨hxy, heqxy⟩ := (baseChange_pointRel_iff P hφ f _ x y).mp hxy
    obtain ⟨hyz, heqyz⟩ := (baseChange_pointRel_iff P hφ f _ y z).mp hyz
    exact (baseChange_pointRel_iff P hφ f _ x z).mpr
      ⟨(hP T σ).trans hxy hyz, heqxy.trans heqyz⟩

end IsPreEquivalence

/-- Base change preserves the equivalence-relation condition on the projections. -/
theorem isEquivalenceRelation_baseChange {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) [IsEquivalenceRelation P.t P.s] :
    IsEquivalenceRelation (P.baseChange hφ f).t (P.baseChange hφ f).s := by
  apply (isEquivalenceRelation_iff (P.baseChange hφ f)).mpr
  exact ⟨monoHom_baseChange P hφ f,
    ((isEquivalenceRelation_iff P).mp inferInstance).2.baseChange hφ f⟩

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
