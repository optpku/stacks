/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# A golden-integer quasi-section of the localized affine line over `ℤ`

This file constructs the closed subscheme `Spec ℤ[φ]` of
`Spec (Localization.Away (X * (X - 1) * (2 * X - 1)))` whose structure
morphism to `Spec ℤ` is finite and surjective, using the affine coordinate
`φ + 1`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Polynomial

namespace AlgebraicGeometry.GoldenIntegerQuasiSection

/-- The minimal polynomial `X ^ 2 - X - 1` of the golden ratio over `ℤ`. -/
def minpoly : ℤ[X] :=
  X ^ 2 - X - 1

/-- The golden-integer order `ℤ[φ] = AdjoinRoot minpoly`. -/
abbrev Order : Type :=
  AdjoinRoot minpoly

/-- The image of `X` in `Order`. -/
def phi : Order :=
  AdjoinRoot.root minpoly

/-- The affine coordinate sent to `φ + 1`. -/
def coord : Order :=
  phi + 1

/-- The inverted element `X * (X - 1) * (2 * X - 1)` of the ambient affine line. -/
def denom : ℤ[X] :=
  X * (X - 1) * (2 * X - 1)

/-- The coordinate ring `ℤ[X][1 / (X * (X - 1) * (2 * X - 1))]`. -/
abbrev CoordinateRing : Type :=
  Localization.Away denom

/-- Evaluation of polynomials in `ℤ[X]` at `coord`. -/
def evalAtCoord : ℤ[X] →+* Order :=
  (aeval coord).toRingHom

/-- The defining quadratic relation of the golden-integer generator. -/
theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h : (X ^ 2 - X - 1 : ℤ[X]).eval₂ (algebraMap ℤ Order) phi = 0 :=
    AdjoinRoot.eval₂_root minpoly
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one] at h
  rw [sub_sub] at h
  exact sub_eq_zero.mp h

/-- The prescribed inverse of the evaluated denominator satisfies the inverse law. -/
theorem denom_mul_inv : evalAtCoord denom * (phi - 1) ^ 6 = 1 := by
  have hphi : phi * (phi - 1) = 1 := by
    calc
      phi * (phi - 1) = phi ^ 2 - phi := by ring
      _ = 1 := by rw [phi_sq]; ring
  have hcube : phi ^ 2 * phi = 2 * phi + 1 := by
    calc
      phi ^ 2 * phi = (phi + 1) * phi := by rw [phi_sq]
      _ = phi ^ 2 + phi := by ring
      _ = 2 * phi + 1 := by rw [phi_sq]; ring
  have hdenom : evalAtCoord denom = phi ^ 6 := by
    calc
      evalAtCoord denom = (phi + 1) * phi * (2 * phi + 1) := by
        change denom.eval₂ (algebraMap ℤ Order) coord = _
        simp only [denom, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one, eval₂_ofNat, coord]
        ring
      _ = phi ^ 2 * phi * (phi ^ 2 * phi) := by rw [← phi_sq, ← hcube]
      _ = phi ^ 6 := by ring
  rw [hdenom, ← mul_pow, hphi, one_pow]

/-- The explicit unit with value `evalAtCoord denom` and inverse `(φ - 1) ^ 6`. -/
def denomUnit : Orderˣ where
  val := evalAtCoord denom
  inv := (phi - 1) ^ 6
  val_inv := denom_mul_inv
  inv_val := by rw [mul_comm]; exact denom_mul_inv

/-- The ring map of the closed immersion, sending `X` to `coord`. -/
def coordinateRingHom : CoordinateRing →+* Order :=
  Localization.awayLift evalAtCoord denom denomUnit.isUnit

/-- The ambient localized affine line
`Spec ℤ[X][1 / (X * (X - 1) * (2 * X - 1))]`. -/
def ambient : Scheme :=
  Spec (CommRingCat.of CoordinateRing)

/-- The closed subscheme `Spec ℤ[φ]`. -/
def scheme : Scheme :=
  Spec (CommRingCat.of Order)

/-- The closed immersion `scheme ⟶ ambient`. -/
def closedImmersion : scheme ⟶ ambient :=
  Spec.map (CommRingCat.ofHom coordinateRingHom)

/-- The structure morphism `scheme ⟶ Spec ℤ`. -/
def toSpecInt : scheme ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ Order))

/-- The structure morphism of the ambient localized affine line. -/
def ambientToSpecInt : ambient ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ CoordinateRing))

/-- `coordinateRingHom` sends the affine coordinate `X` to `coord`. -/
theorem coordinateRingHom_map_X :
    coordinateRingHom (algebraMap ℤ[X] CoordinateRing X) = coord := by
  simp [coordinateRingHom, Localization.awayLift, evalAtCoord]

/-- The structure morphism of `scheme` factors as the closed immersion
followed by the structure morphism of `ambient`. -/
theorem toSpecInt_eq_comp :
    toSpecInt = closedImmersion ≫ ambientToSpecInt := by
  unfold toSpecInt closedImmersion ambientToSpecInt scheme ambient
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- `closedImmersion` is a closed immersion. -/
instance instIsClosedImmersion : IsClosedImmersion closedImmersion := by
  apply IsClosedImmersion.spec_of_surjective
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨algebraMap ℤ[X] CoordinateRing (p.comp (X - 1)), ?_⟩
  simp [coordinateRingHom, Localization.awayLift, evalAtCoord, aeval_comp,
    coord, phi, AdjoinRoot.aeval_eq]

/-- The defining quadratic polynomial is monic. -/
theorem minpoly_monic : minpoly.Monic := by
  unfold minpoly
  monicity!

/-- The structure morphism `toSpecInt` is finite. -/
instance instIsFinite_toSpecInt : IsFinite toSpecInt := by
  unfold toSpecInt scheme
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  exact minpoly_monic.finite_adjoinRoot

/-- The structure morphism `toSpecInt` is surjective. -/
instance instSurjective_toSpecInt : Surjective toSpecInt := by
  have hdeg : minpoly.degree ≠ 0 := by
    have hd : minpoly.degree = 2 := by
      unfold minpoly
      compute_degree!
    rw [hd]
    decide
  letI : Module.Finite ℤ Order := minpoly_monic.finite_adjoinRoot
  letI : FaithfulSMul ℤ Order :=
    (faithfulSMul_iff_algebraMap_injective ℤ Order).mpr
      (AdjoinRoot.of.injective_of_degree_ne_zero hdeg)
  exact ⟨Algebra.IsIntegral.comap_surjective ℤ Order⟩

end AlgebraicGeometry.GoldenIntegerQuasiSection
