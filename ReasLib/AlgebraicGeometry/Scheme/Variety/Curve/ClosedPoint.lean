/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RegularLocus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.RingTheory.Normal.RegularLocal

/-!
# Closed points of curves

This module relates regularity of the local ring at a closed point of a curve
to normality, the discrete valuation ring condition, the defining ideal
sheaf, the effective-Cartier condition, and pointwise smoothness.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Curve.ClosedPoint

open Scheme
open Scheme.IdealSheafData
open SheafOfModules

variable {k : Type u} [Field k]

section

variable (X : Over (Spec (CommRingCat.of k))) [Curve X]

/-- At a closed point of a curve over a field, regularity and normality of the local ring,
the discrete valuation ring condition, invertibility of the reduced point's defining ideal
sheaf, and the effective-Cartier condition are equivalent. -/
theorem regularity_tfae (x : X.left) (hx : x ∈ closedPoints X.left) :
    let Y := X.left
    let D : Y.IdealSheafData :=
      IdealSheafData.vanishingIdeal
        ⟨({x} : Set Y), by simpa [closedPoints] using hx⟩
    let F := Y.presheaf
    let ℐ : Y.Modules :=
      kernel (unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)
    List.TFAE
      [ IsRegularLocalRing (F.stalk x),
        IsNormalRing (F.stalk x),
        IsDiscreteValuationRing (F.stalk x),
        Scheme.Modules.Invertible ℐ,
        AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ] := sorry

/-- At a closed point of a curve over a field, if the field is perfect or the residue-field
extension is separable, regularity and normality of the local ring, the discrete valuation
ring condition, invertibility of the reduced point's defining ideal sheaf, the
effective-Cartier condition, and smoothness at the point are equivalent. -/
theorem regularity_smoothAt_tfae
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (hperf_or_sep : PerfectField k ∨ Algebra.IsSeparable k (X.left.residueField x)) :
    let Y := X.left
    let D : Y.IdealSheafData :=
      IdealSheafData.vanishingIdeal
        ⟨({x} : Set Y), by simpa [closedPoints] using hx⟩
    let F := Y.presheaf
    let ℐ : Y.Modules :=
      kernel (unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)
    List.TFAE
      [ IsRegularLocalRing (F.stalk x),
        IsNormalRing (F.stalk x),
        IsDiscreteValuationRing (F.stalk x),
        Scheme.Modules.Invertible ℐ,
        AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι,
        X.hom.SmoothAt x ] := sorry

end

/- The following declarations provide the reduced closed-point ideal and its
open complement used by the punctured-curve Picard API. -/

open Scheme
open Scheme.IdealSheafData

/-- The reduced ideal sheaf of a closed singleton. -/
def closedPointIdeal {X : Scheme.{u}} (x : X) (hx : x ∈ closedPoints X) :
    X.IdealSheafData :=
  vanishingIdeal ⟨({x} : Set X), hx⟩

/-- The reduced closed-point ideal is the vanishing ideal of the closed singleton. -/
theorem closedPointIdeal_eq {X : Scheme.{u}} (x : X) (hx : x ∈ closedPoints X) :
    closedPointIdeal x hx = vanishingIdeal ⟨({x} : Set X), hx⟩ :=
  sorry

/-- The support of the reduced closed-point ideal is the closed singleton. -/
theorem support_closedPointIdeal {X : Scheme.{u}} (x : X)
    (hx : x ∈ closedPoints X) :
    (closedPointIdeal x hx).support = ⟨({x} : Set X), hx⟩ :=
  sorry

/-- The open complement of a closed point, namely the complement of its singleton. -/
def closedPointOpenComplement {X : Scheme.{u}} (x : X)
    (hx : x ∈ closedPoints X) : X.Opens :=
  (closedPointIdeal x hx).openComplement

/-- The open complement of a closed point is the set-theoretic complement of the singleton. -/
theorem coe_closedPointOpenComplement {X : Scheme.{u}} (x : X)
    (hx : x ∈ closedPoints X) :
    (closedPointOpenComplement x hx : Set X) = {x}ᶜ :=
  sorry

/-- On a smooth curve, the reduced closed point is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_closedPointIdeal
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    (x : X.left) (hx : x ∈ closedPoints X.left) :
    IsEffectiveCartierDivisor (closedPointIdeal x hx).subschemeι :=
  sorry

end AlgebraicGeometry.Curve.ClosedPoint

namespace AlgebraicGeometry.Curve

/-- A smooth proper curve over a field with constant global functions and genus `g ≥ 2`
has a closed point whose residue field is finite-dimensional and separable over the base
field, of degree at most `2 * g - 2`. -/
theorem exists_closedPoint_finrank_le_two_mul_genus_sub_two
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Smooth X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (g : ℕ)
    (h_genus : g = SchemeOverField.genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ)
    (h_g : 2 ≤ g) :
    ∃ x : X.left, x ∈ closedPoints X.left ∧
      FiniteDimensional k (X.left.residueField x) ∧
      Algebra.IsSeparable k (X.left.residueField x) ∧
      Module.finrank k (X.left.residueField x) ≤ 2 * g - 2 := sorry

end AlgebraicGeometry.Curve
