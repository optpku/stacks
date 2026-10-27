/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrow
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.DualNumber
public import ReasLib.RingTheory.DualNumber.Scale
public import ReasLib.RingTheory.DualNumberPair

/-!
# Operations on dotted tangent arrows

This leaf defines the pairing, addition, and scalar multiplication operations
on dotted tangent arrows and compares them with their transported algebraic
structures.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory DualNumberPair
open scoped DualNumber DualNumberPair

universe u

namespace AlgebraicGeometry.Scheme.Hom

noncomputable section

variable {X S : Scheme.{u}} {f : X ⟶ S} {x : X}

/-- A dotted tangent arrow sends the closed point of its dual-number spectrum
to its specified point. -/
theorem closedPoint_eq (θ : DottedTangentArrow f x) :
    θ.1 (IsLocalRing.closedPoint (CommRingCat.of ((X.residueField x)[ε]))) = x :=
  by
    let q : (X.residueField x)[ε] →+* X.residueField x :=
      (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
        (X.residueField x)).toRingHom
    let hq : IsLocalHom q :=
      IsLocalHom.of_surjective q fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩
    have hclosed :
        dualNumberPointInclusion x
            (IsLocalRing.closedPoint (CommRingCat.of (X.residueField x))) =
          IsLocalRing.closedPoint
            (CommRingCat.of ((X.residueField x)[ε])) := by
      simpa [dualNumberPointInclusion, q] using
        (@Spec_closedPoint (CommRingCat.of ((X.residueField x)[ε]))
          (CommRingCat.of (X.residueField x)) _ _ (CommRingCat.ofHom q) hq)
    have h := congrArg
      (fun g ↦ g (IsLocalRing.closedPoint (CommRingCat.of (X.residueField x)))) θ.2.1
    rw [Scheme.Hom.comp_apply, hclosed] at h
    exact h.trans (Scheme.fromSpecResidueField_apply x _)

/-- The local ring homomorphism carried by a dotted tangent arrow, obtained by
transporting the stalk map at its closed point. -/
def dottedArrowRingHom (θ : DottedTangentArrow f x) :
    X.presheaf.stalk x →+* (X.residueField x)[ε] :=
  let q : (X.residueField x)[ε] →+* X.residueField x :=
    (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
      (X.residueField x)).toRingHom
  let hq : IsLocalHom q :=
    IsLocalHom.of_surjective q fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩
  let hclosed :
      dualNumberPointInclusion x
          (IsLocalRing.closedPoint (CommRingCat.of (X.residueField x))) =
        IsLocalRing.closedPoint
          (CommRingCat.of ((X.residueField x)[ε])) := by
    simpa [dualNumberPointInclusion, q] using
      (@Spec_closedPoint (CommRingCat.of ((X.residueField x)[ε]))
        (CommRingCat.of (X.residueField x)) _ _ (CommRingCat.ofHom q) hq)
  let h := congrArg
    (fun g ↦ g (IsLocalRing.closedPoint (CommRingCat.of (X.residueField x)))) θ.2.1
  let hp :
      θ.1 (IsLocalRing.closedPoint (CommRingCat.of ((X.residueField x)[ε]))) = x := by
    rw [Scheme.Hom.comp_apply, hclosed] at h
    exact h.trans (Scheme.fromSpecResidueField_apply x _)
  ((X.presheaf.stalkCongr (.of_eq hp.symm)).hom ≫
      Scheme.stalkClosedPointTo θ.1).hom

/-- The local ring homomorphism reconstructs its dotted tangent arrow. -/
theorem dottedArrowRingHom_spec (θ : DottedTangentArrow f x) :
    Spec.map (CommRingCat.ofHom (dottedArrowRingHom θ)) ≫ X.fromSpecStalk x = θ.1 := by
  change Spec.map
    ((X.presheaf.stalkCongr (.of_eq (closedPoint_eq θ).symm)).hom ≫
      Scheme.stalkClosedPointTo θ.1) ≫ X.fromSpecStalk x = θ.1
  rw [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- The constant coefficient of a dotted-arrow stalk map is the residue map. -/
theorem dottedArrowRingHom_fst (θ : DottedTangentArrow f x)
    (a : X.presheaf.stalk x) :
    (dottedArrowRingHom θ a).fst = X.residue x a := by
  have h :
      CommRingCat.ofHom (dottedArrowRingHom θ) ≫
        CommRingCat.ofHom
          (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
            (X.residueField x)).toRingHom = X.residue x := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, dottedArrowRingHom_spec]
    exact θ.2.1
  exact congrArg (fun g ↦ g a) h

/-- The coefficientwise pairing of two dotted-arrow stalk maps into the pair
of square-zero directions. -/
def pairToFun (θ₁ θ₂ : DottedTangentArrow f x) (a : X.presheaf.stalk x) :
    DualNumberPair (X.residueField x) :=
  let φ₁ := dottedArrowRingHom θ₁ a
  let φ₂ := dottedArrowRingHom θ₂ a
  (φ₁.fst, (φ₁.snd, φ₂.snd))

/-- The pairing of dotted-arrow stalk maps preserves the multiplicative unit. -/
theorem pairToFun_map_one (θ₁ θ₂ : DottedTangentArrow f x) :
    pairToFun θ₁ θ₂ 1 = 1 :=
  by
    ext <;> simp [pairToFun]

/-- The pairing of dotted-arrow stalk maps preserves multiplication. -/
theorem pairToFun_map_mul (θ₁ θ₂ : DottedTangentArrow f x)
    (a b : X.presheaf.stalk x) :
    pairToFun θ₁ θ₂ (a * b) = pairToFun θ₁ θ₂ a * pairToFun θ₁ θ₂ b :=
  by
    ext <;> simp [pairToFun, map_mul, dottedArrowRingHom_fst]

/-- The pairing of dotted-arrow stalk maps preserves zero. -/
theorem pairToFun_map_zero (θ₁ θ₂ : DottedTangentArrow f x) :
    pairToFun θ₁ θ₂ 0 = 0 :=
  by
    ext <;> simp [pairToFun]

/-- The pairing of dotted-arrow stalk maps preserves addition. -/
theorem pairToFun_map_add (θ₁ θ₂ : DottedTangentArrow f x)
    (a b : X.presheaf.stalk x) :
    pairToFun θ₁ θ₂ (a + b) = pairToFun θ₁ θ₂ a + pairToFun θ₁ θ₂ b :=
  by
    ext <;> simp [pairToFun, map_add]

/-- The ring homomorphism pairing two dotted tangent arrows. -/
def pairRingHom (θ₁ θ₂ : DottedTangentArrow f x) :
    X.presheaf.stalk x →+* DualNumberPair (X.residueField x) where
  toFun := pairToFun θ₁ θ₂
  map_one' := pairToFun_map_one θ₁ θ₂
  map_mul' := pairToFun_map_mul θ₁ θ₂
  map_zero' := pairToFun_map_zero θ₁ θ₂
  map_add' := pairToFun_map_add θ₁ θ₂

/-- The morphism from the spectrum of the pair of square-zero directions to
the scheme induced by two dotted tangent arrows. -/
def pair (θ₁ θ₂ : DottedTangentArrow f x) :
    Spec (CommRingCat.of (DualNumberPair (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (pairRingHom θ₁ θ₂)) ≫ X.fromSpecStalk x

/-- Two dotted tangent arrows agree after restriction to the closed point. -/
theorem pair_compat (θ₁ θ₂ : DottedTangentArrow f x) :
    fromClosedPoint (X.residueField x) ≫ θ₁.1 =
      fromClosedPoint (X.residueField x) ≫ θ₂.1 :=
  θ₁.2.1.trans θ₂.2.1.symm

/-- The first pushout leg of the pairing morphism recovers the first arrow. -/
theorem inl_pair (θ₁ θ₂ : DottedTangentArrow f x) :
    inl (X.residueField x) ≫ pair θ₁ θ₂ = θ₁.1 :=
  by
    have h : (projFst (X.residueField x)).toRingHom.comp (pairRingHom θ₁ θ₂) =
        dottedArrowRingHom θ₁ := by
      apply RingHom.ext
      intro a
      apply TrivSqZeroExt.ext <;> simp [projFst, pairRingHom, pairToFun]
    rw [inl, pair, ← Spec.map_comp_assoc]
    change Spec.map (CommRingCat.ofHom
      ((projFst (X.residueField x)).toRingHom.comp (pairRingHom θ₁ θ₂))) ≫
        X.fromSpecStalk x = θ₁.1
    rw [h, dottedArrowRingHom_spec]

/-- The second pushout leg of the pairing morphism recovers the second arrow. -/
theorem inr_pair (θ₁ θ₂ : DottedTangentArrow f x) :
    inr (X.residueField x) ≫ pair θ₁ θ₂ = θ₂.1 :=
  by
    have h : (projSnd (X.residueField x)).toRingHom.comp (pairRingHom θ₁ θ₂) =
        dottedArrowRingHom θ₂ := by
      apply RingHom.ext
      intro a
      apply TrivSqZeroExt.ext <;>
        simp [projSnd, pairRingHom, pairToFun, dottedArrowRingHom_fst]
    rw [inr, pair, ← Spec.map_comp_assoc]
    change Spec.map (CommRingCat.ofHom
      ((projSnd (X.residueField x)).toRingHom.comp (pairRingHom θ₁ θ₂))) ≫
        X.fromSpecStalk x = θ₂.1
    rw [h, dottedArrowRingHom_spec]

/-- The pairing morphism is the unique descent through the dual-number
pushout. -/
theorem pair_eq_desc (θ₁ θ₂ : DottedTangentArrow f x) :
    pair θ₁ θ₂ =
      (spec_isPushout (X.residueField x)).desc θ₁.1 θ₂.1 (pair_compat θ₁ θ₂) :=
  by
    apply (spec_isPushout (X.residueField x)).hom_ext
    · rw [inl_pair, IsPushout.inl_desc]
    · rw [inr_pair, IsPushout.inr_desc]

/-- The composite defining tangent addition preserves the specified point. -/
theorem tangentAdd_closedPoint (θ₁ θ₂ : DottedTangentArrow f x) :
    dualNumberPointInclusion x ≫ DualNumberPair.sum (X.residueField x) ≫ pair θ₁ θ₂ =
      X.fromSpecResidueField x :=
  by
    have h : dualNumberPointInclusion x ≫ DualNumberPair.sum (X.residueField x) =
        dualNumberPointInclusion x ≫ inl (X.residueField x) := by
      rw [dualNumberPointInclusion, DualNumberPair.sum, inl,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
    rw [← Category.assoc, h, Category.assoc, inl_pair]
    exact θ₁.2.1

/-- The composite defining tangent addition remains over the base scheme. -/
theorem tangentAdd_over (θ₁ θ₂ : DottedTangentArrow f x) :
    (DualNumberPair.sum (X.residueField x) ≫ pair θ₁ θ₂) ≫ f =
      dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x) :=
  by
    let q : S.presheaf.stalk (f x) ⟶ CommRingCat.of ((X.residueField x)[ε]) :=
      S.residue (f x) ≫ CommRingCat.ofHom
        (algebraMap (S.residueField (f x)) ((X.residueField x)[ε]))
    have hq_spec : Spec.map q ≫ S.fromSpecStalk (f x) =
        dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x) := by
      simp only [q, Spec.map_comp, Scheme.fromSpecResidueField,
        dualNumberToBasePoint, Category.assoc]
      rfl
    have hθ (θ : DottedTangentArrow f x) :
        f.stalkMap x ≫ CommRingCat.ofHom (dottedArrowRingHom θ) = q := by
      apply Spec.map_injective
      apply (cancel_mono (S.fromSpecStalk (f x))).mp
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        ← Category.assoc]
      refine (congrArg (fun g ↦ g ≫ f) (dottedArrowRingHom_spec θ)).trans ?_
      exact θ.2.2.trans hq_spec.symm
    have hring :
        f.stalkMap x ≫ CommRingCat.ofHom (pairRingHom θ₁ θ₂) ≫
          CommRingCat.ofHom (sumAlgHom (X.residueField x)).toRingHom = q := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      have h₁ := congrArg (fun g ↦ g a) (hθ θ₁)
      have h₂ := congrArg (fun g ↦ g a) (hθ θ₂)
      change dottedArrowRingHom θ₁ (f.stalkMap x a) = q a at h₁
      change dottedArrowRingHom θ₂ (f.stalkMap x a) = q a at h₂
      have hq : (q a).snd = 0 := by
        change (algebraMap (S.residueField (f x)) ((X.residueField x)[ε])
          (S.residue (f x) a)).snd = 0
        simp [TrivSqZeroExt.algebraMap_eq_inl']
      change sumAlgHom (X.residueField x) (pairRingHom θ₁ θ₂ (f.stalkMap x a)) = q a
      apply TrivSqZeroExt.ext <;>
        simp [sumAlgHom, pairRingHom, pairToFun, h₁, h₂, hq]
    calc
      (DualNumberPair.sum (X.residueField x) ≫ pair θ₁ θ₂) ≫ f =
          Spec.map (f.stalkMap x ≫ CommRingCat.ofHom (pairRingHom θ₁ θ₂) ≫
            CommRingCat.ofHom (sumAlgHom (X.residueField x)).toRingHom) ≫
              S.fromSpecStalk (f x) := by
        simp only [DualNumberPair.sum, pair, Spec.map_comp, Category.assoc,
          Scheme.SpecMap_stalkMap_fromSpecStalk]
        rfl
      _ = Spec.map q ≫ S.fromSpecStalk (f x) := by rw [hring]
      _ = dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x) := hq_spec

/-- Addition of two dotted tangent arrows obtained by pairing them and applying
the sum map on dual numbers. -/
def tangentAdd (θ₁ θ₂ : DottedTangentArrow f x) : DottedTangentArrow f x :=
  ⟨DualNumberPair.sum (X.residueField x) ≫ pair θ₁ θ₂,
    tangentAdd_closedPoint θ₁ θ₂, tangentAdd_over θ₁ θ₂⟩

/-- The composite defining tangent scalar multiplication preserves the
specified point. -/
theorem tangentSmul_closedPoint (c : X.residueField x) (θ : DottedTangentArrow f x) :
    dualNumberPointInclusion x ≫ DualNumber.scale c ≫ θ.1 =
      X.fromSpecResidueField x :=
  by
    have h : dualNumberPointInclusion x ≫ DualNumber.scale c =
        dualNumberPointInclusion x := by
      rw [dualNumberPointInclusion, DualNumber.scale, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change (DualNumber.scaleAlgHom c a).fst = a.fst
      exact TrivSqZeroExt.fst_map _ _
    rw [← Category.assoc, h]
    exact θ.2.1

/-- The composite defining tangent scalar multiplication remains over the base
scheme. -/
theorem tangentSmul_over (c : X.residueField x) (θ : DottedTangentArrow f x) :
    (DualNumber.scale c ≫ θ.1) ≫ f =
      dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x) :=
  by
    have h : DualNumber.scale c ≫ dualNumberToBasePoint f x =
        dualNumberToBasePoint f x := by
      rw [DualNumber.scale, dualNumberToBasePoint, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change DualNumber.scaleAlgHom c
          (algebraMap (S.residueField (f x)) ((X.residueField x)[ε]) a) =
        algebraMap (S.residueField (f x)) ((X.residueField x)[ε]) a
      simp [DualNumber.scaleAlgHom, TrivSqZeroExt.algebraMap_eq_inl']
    rw [Category.assoc, θ.2.2, ← Category.assoc, h]

/-- Scalar multiplication of a dotted tangent arrow obtained by applying the
dual-number scaling map. -/
def tangentSmul (c : X.residueField x) (θ : DottedTangentArrow f x) :
    DottedTangentArrow f x :=
  ⟨DualNumber.scale c ≫ θ.1, tangentSmul_closedPoint c θ, tangentSmul_over c θ⟩

/-- Geometric addition agrees with the canonical additive structure on dotted
tangent arrows. -/
theorem tangentAdd_eq_add (θ₁ θ₂ : DottedTangentArrow f x) :
    tangentAdd θ₁ θ₂ = θ₁ + θ₂ :=
  by
    apply Subtype.ext
    change DualNumberPair.sum (X.residueField x) ≫ pair θ₁ θ₂ = _
    rw [DualNumberPair.sum, pair, ← Spec.map_comp_assoc]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change sumAlgHom (X.residueField x) (pairRingHom θ₁ θ₂ a) =
      (X.residue x a, (dottedArrowRingHom θ₁ a).snd + (dottedArrowRingHom θ₂ a).snd)
    apply TrivSqZeroExt.ext
    · change _ = X.residue x a
      simpa [sumAlgHom, pairRingHom, pairToFun] using dottedArrowRingHom_fst θ₁ a
    · change _ = (dottedArrowRingHom θ₁ a).snd + (dottedArrowRingHom θ₂ a).snd
      simp [sumAlgHom, pairRingHom, pairToFun]

/-- Geometric scalar multiplication agrees with the canonical module structure
on dotted tangent arrows. -/
theorem tangentSmul_eq_smul (c : X.residueField x) (θ : DottedTangentArrow f x) :
    tangentSmul c θ = c • θ :=
  by
    apply Subtype.ext
    change DualNumber.scale c ≫ θ.1 = _
    rw [← dottedArrowRingHom_spec θ, DualNumber.scale, ← Spec.map_comp_assoc]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change DualNumber.scaleAlgHom c (dottedArrowRingHom θ a) =
      (X.residue x a, c • (dottedArrowRingHom θ a).snd)
    apply TrivSqZeroExt.ext
    · change _ = X.residue x a
      simpa [DualNumber.scaleAlgHom] using dottedArrowRingHom_fst θ a
    · change _ = c • (dottedArrowRingHom θ a).snd
      simp [DualNumber.scaleAlgHom, LinearMap.toSpanSingleton_apply, mul_comm]

end

end AlgebraicGeometry.Scheme.Hom
