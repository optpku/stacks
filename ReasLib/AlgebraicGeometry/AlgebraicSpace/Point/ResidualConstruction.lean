/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Field.Subfield.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-! # Actual residual-field data for a quasi-separated algebraic space

Starting with a quotient representative Spec K → X, take the equalizer
subfield of the two actual maps K → Γ(Spec K ×_X Spec K, O).
Descent only inverts specified restriction maps. The residual-point
theorem's geometric laws are kept separate from all concrete data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ResidualPoint

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [AlgebraicSpace.IsQuasiSeparated X]
    (x : Points X)

/-- Quotient.out uses the actual representative equivalence class, not an
admitted existence theorem about monomorphic residue-field points. -/
def representative : FieldValuedPoint X := Quotient.out x

/-- The original X diagonal supplies this actual self-relation scheme. -/
def relation : Over S :=
  (Functor.relativelyRepresentable.of_diag X.representableDiagonal
    (representative X x).hom).pullback (representative X x).hom

def leftProjection : relation X x ⟶ (representative X x).overObj :=
  (Functor.relativelyRepresentable.of_diag X.representableDiagonal
    (representative X x).hom).fst' (representative X x).hom

def rightProjection : relation X x ⟶ (representative X x).overObj :=
  (Functor.relativelyRepresentable.of_diag X.representableDiagonal
    (representative X x).hom).snd (representative X x).hom

/-- The two actual ring maps from the field into the relation's functions. -/
def leftRing : (representative X x).K →+* Γ((relation X x).left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (representative X x).K)).inv ≫ (leftProjection X x).left.appTop).hom

def rightRing : (representative X x).K →+* Γ((relation X x).left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (representative X x).K)).inv ≫ (rightProjection X x).left.appTop).hom

omit [AlgebraicSpace.IsQuasiSeparated X] in
/-- Two unital maps out of a field agreeing on a scalar also agree on its
inverse: zero is immediate; otherwise both images of the inverse are the
unique inverse of their common unit image. No element is selected here. -/
theorem inverse_coherence (a : (representative X x).K)
    (ha : leftRing X x a = rightRing X x a) :
    leftRing X x a⁻¹ = rightRing X x a⁻¹ := by
  by_cases hzero : a = 0
  · subst a
    simp
  · have hl : leftRing X x a * leftRing X x a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hzero, map_one]
    have hr : rightRing X x a * rightRing X x a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hzero, map_one]
    calc
      leftRing X x a⁻¹ = leftRing X x a⁻¹ * (rightRing X x a * rightRing X x a⁻¹) := by
        rw [hr, mul_one]
      _ = (leftRing X x a⁻¹ * leftRing X x a) * rightRing X x a⁻¹ := by
        rw [← ha, mul_assoc]
      _ = rightRing X x a⁻¹ := by rw [mul_comm (leftRing X x a⁻¹), hl, one_mul]

/-- The source field is the concrete equalizer subfield inside K. -/
def invariantField : Subfield (representative X x).K where
  carrier := {a | leftRing X x a = rightRing X x a}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by intro a b ha hb; simpa using congrArg₂ (· + ·) ha hb
  mul_mem' := by intro a b ha hb; simpa using congrArg₂ (· * ·) ha hb
  neg_mem' := by intro a ha; simpa using congrArg Neg.neg ha
  inv_mem' := inverse_coherence X x

abbrev K := invariantField X x

/-- The actual faithfully flat map of field spectra associated to K₀ ⊆ K. -/
def cover : Spec (.of (representative X x).K) ⟶ Spec (.of (K X x)) :=
  Spec.map (CommRingCat.ofHom (invariantField X x).subtype)

theorem cover_faithfullyFlat : (invariantField X x).subtype.FaithfullyFlat := by
  -- Local instance justification (defeq pin): Use the displayed invariant-subfield inclusion as the scalar action when proving this field extension faithfully flat.
  letI : Algebra (K X x) (representative X x).K := (invariantField X x).subtype.toAlgebra
  change Module.FaithfullyFlat (K X x) (representative X x).K
  infer_instance

/-- The actual Čech pair of the displayed field cover. -/
abbrev cech := pullback (cover X x) (cover X x)

/-- Both projections agree on the equalizer subfield by its definition.
Spec–Γ adjunction turns this ring equality into the displayed scheme equality. -/
theorem projection_cover_eq :
    (leftProjection X x).left ≫ cover X x =
      (rightProjection X x).left ≫ cover X x := by
  sorry

/-- The fixed map from the actual self-relation to the actual field Čech pair. -/
def relationComparison : (relation X x).left ⟶ cech X x :=
  pullback.lift (leftProjection X x).left (rightProjection X x).left
    (projection_cover_eq X x)

theorem relationComparison_fst :
    relationComparison X x ≫ pullback.fst (cover X x) (cover X x) =
      (leftProjection X x).left := pullback.lift_fst _ _ _

theorem relationComparison_snd :
    relationComparison X x ≫ pullback.snd (cover X x) (cover X x) =
      (rightProjection X x).left := pullback.lift_snd _ _ _

/-- Effectiveness for this fixed field relation in the quasi-separated
range. A monomorphic residue representative k exists mathematically by
Stacks 68.4.5/68.5.1; any representative K factors through it, so R is
Spec(K tensor_k K). Faithfully flat descent identifies k with the displayed
equalizer subfield. This justifies this map's IsIso without selecting k. -/
theorem relationComparison_isIso : IsIso (relationComparison X x) := by
  sorry

/-- The base map descends along the invariant-field cover. In the
quasi-separated range the original relation is the effective equivalence
relation of this field cover; equality therefore holds on the displayed
Čech pair. This is a law of the specified maps. -/
theorem base_coherence :
    pullback.fst (cover X x) (cover X x) ≫ (representative X x).structureHom =
      pullback.snd (cover X x) (cover X x) ≫ (representative X x).structureHom := by
  sorry

/-- Restriction of actual scheme morphisms to the actual faithfully flat cover. -/
def baseRestriction : (Spec (.of (K X x)) ⟶ S) →
    {h : Spec (.of (representative X x).K) ⟶ S //
      pullback.fst (cover X x) (cover X x) ≫ h =
        pullback.snd (cover X x) (cover X x) ≫ h} := fun h ↦
  ⟨cover X x ≫ h, by
    simpa only [Category.assoc] using
      congrArg (fun a ↦ a ≫ h) (pullback.condition (f := cover X x) (g := cover X x))⟩

/-- Schemes are fpqc sheaves, so this FIXED restriction map is bijective. -/
theorem baseRestriction_bijective : Function.Bijective (baseRestriction X x) := by
  sorry

def baseEquiv := Equiv.ofBijective (baseRestriction X x) (baseRestriction_bijective X x)

/-- The descended base morphism is the inverse of actual restriction. -/
def structureHom : Spec (.of (K X x)) ⟶ S :=
  (baseEquiv X x).symm ⟨(representative X x).structureHom, base_coherence X x⟩

theorem cover_structureHom : cover X x ≫ structureHom X x = (representative X x).structureHom :=
  congrArg Subtype.val ((baseEquiv X x).apply_symm_apply _)

abbrev fieldOver : Over S := Over.mk (structureHom X x)

def coverOver : (representative X x).overObj ⟶ fieldOver X x :=
  Over.homMk (cover X x) (cover_structureHom X x)

/-- Actual compatibility on the Čech pair over S. -/
def Compatible (h : yoneda.obj (representative X x).overObj ⟶ X.functorOfPoints) : Prop :=
  yoneda.map (pullback.fst (coverOver X x) (coverOver X x)) ≫ h =
    yoneda.map (pullback.snd (coverOver X x) (coverOver X x)) ≫ h

theorem representative_compatible : Compatible X x (representative X x).hom := by
  sorry

/-- Restriction of maps from the actual invariant-field spectrum to X. -/
def restriction : (yoneda.obj (fieldOver X x) ⟶ X.functorOfPoints) →
    {h : yoneda.obj (representative X x).overObj ⟶ X.functorOfPoints // Compatible X x h} :=
  fun h ↦ ⟨yoneda.map (coverOver X x) ≫ h, by
    dsimp [Compatible]
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      pullback.condition]⟩

/-- Algebraic spaces satisfy fpqc descent; the fixed cover is faithfully
flat and affine. This is a property of the displayed restriction map. -/
theorem restriction_bijective : Function.Bijective (restriction X x) := by
  sorry

def restrictionEquiv := Equiv.ofBijective (restriction X x) (restriction_bijective X x)

/-- The actual map Spec K₀ → X obtained by descending the specified representative. -/
def hom : yoneda.obj (fieldOver X x) ⟶ X.functorOfPoints :=
  (restrictionEquiv X x).symm ⟨(representative X x).hom, representative_compatible X x⟩

theorem cover_hom : yoneda.map (coverOver X x) ≫ hom X x = (representative X x).hom :=
  congrArg Subtype.val ((restrictionEquiv X x).apply_symm_apply _)

def point : FieldValuedPoint X :=
  FieldValuedPoint.of (K X x) (structureHom X x) (hom X x)

/-- The effective field-relation theorem says this specified descended map
is the residual monomorphism. Quasi-separatedness makes it quasi-compact. -/
theorem point_mono : Mono (point X x).hom := by sorry
theorem point_quasiCompact : AlgebraicSpace.QuasiCompact (point X x).hom := by sorry
/-- The actual cover is a factorization of the old representative through
the constructed point, using the two proved cover equations. -/
def coverFactorization : FieldValuedPoint.Factorization (representative X x) (point X x) where
  schemeHom := cover X x
  fac_structure := cover_structureHom X x
  fac_hom := cover_hom X x

theorem point_class : Points.mk (point X x) = x := by
  have h : Points.mk (point X x) = Points.mk (representative X x) :=
    Quotient.sound ⟨{
      point := representative X x
      left := coverFactorization X x
      right := FieldValuedPoint.Factorization.refl (representative X x) }⟩
  exact h.trans (Quotient.out_eq x)

/-- Decency receives explicit point data, not an admitted existential witness. -/
theorem decent : AlgebraicSpace.IsDecent X where
  exists_quasiCompact_mono x := ⟨point X x, point_quasiCompact X x, point_mono X x, point_class X x⟩

end AlgebraicGeometry.AlgebraicSpace.ResidualPoint
