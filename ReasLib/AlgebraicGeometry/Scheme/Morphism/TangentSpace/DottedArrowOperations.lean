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
  sorry

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
  sorry

/-- The pairing of dotted-arrow stalk maps preserves multiplication. -/
theorem pairToFun_map_mul (θ₁ θ₂ : DottedTangentArrow f x)
    (a b : X.presheaf.stalk x) :
    pairToFun θ₁ θ₂ (a * b) = pairToFun θ₁ θ₂ a * pairToFun θ₁ θ₂ b :=
  sorry

/-- The pairing of dotted-arrow stalk maps preserves zero. -/
theorem pairToFun_map_zero (θ₁ θ₂ : DottedTangentArrow f x) :
    pairToFun θ₁ θ₂ 0 = 0 :=
  sorry

/-- The pairing of dotted-arrow stalk maps preserves addition. -/
theorem pairToFun_map_add (θ₁ θ₂ : DottedTangentArrow f x)
    (a b : X.presheaf.stalk x) :
    pairToFun θ₁ θ₂ (a + b) = pairToFun θ₁ θ₂ a + pairToFun θ₁ θ₂ b :=
  sorry

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
  sorry

/-- The first pushout leg of the pairing morphism recovers the first arrow. -/
theorem inl_pair (θ₁ θ₂ : DottedTangentArrow f x) :
    inl (X.residueField x) ≫ pair θ₁ θ₂ = θ₁.1 :=
  sorry

/-- The second pushout leg of the pairing morphism recovers the second arrow. -/
theorem inr_pair (θ₁ θ₂ : DottedTangentArrow f x) :
    inr (X.residueField x) ≫ pair θ₁ θ₂ = θ₂.1 :=
  sorry

/-- The pairing morphism is the unique descent through the dual-number
pushout. -/
theorem pair_eq_desc (θ₁ θ₂ : DottedTangentArrow f x) :
    pair θ₁ θ₂ =
      (spec_isPushout (X.residueField x)).desc θ₁.1 θ₂.1 (pair_compat θ₁ θ₂) :=
  sorry

/-- The composite defining tangent addition preserves the specified point. -/
theorem tangentAdd_closedPoint (θ₁ θ₂ : DottedTangentArrow f x) :
    dualNumberPointInclusion x ≫ DualNumberPair.sum (X.residueField x) ≫ pair θ₁ θ₂ =
      X.fromSpecResidueField x :=
  sorry

/-- The composite defining tangent addition remains over the base scheme. -/
theorem tangentAdd_over (θ₁ θ₂ : DottedTangentArrow f x) :
    (DualNumberPair.sum (X.residueField x) ≫ pair θ₁ θ₂) ≫ f =
      dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x) :=
  sorry

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
  sorry

/-- The composite defining tangent scalar multiplication remains over the base
scheme. -/
theorem tangentSmul_over (c : X.residueField x) (θ : DottedTangentArrow f x) :
    (DualNumber.scale c ≫ θ.1) ≫ f =
      dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x) :=
  sorry

/-- Scalar multiplication of a dotted tangent arrow obtained by applying the
dual-number scaling map. -/
def tangentSmul (c : X.residueField x) (θ : DottedTangentArrow f x) :
    DottedTangentArrow f x :=
  ⟨DualNumber.scale c ≫ θ.1, tangentSmul_closedPoint c θ, tangentSmul_over c θ⟩

/-- Geometric addition agrees with the canonical additive structure on dotted
tangent arrows. -/
theorem tangentAdd_eq_add (θ₁ θ₂ : DottedTangentArrow f x) :
    tangentAdd θ₁ θ₂ = θ₁ + θ₂ :=
  sorry

/-- Geometric scalar multiplication agrees with the canonical module structure
on dotted tangent arrows. -/
theorem tangentSmul_eq_smul (c : X.residueField x) (θ : DottedTangentArrow f x) :
    tangentSmul c θ = c • θ :=
  sorry

end

end AlgebraicGeometry.Scheme.Hom
