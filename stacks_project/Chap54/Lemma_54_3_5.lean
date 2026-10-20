/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ResidualIdealLength

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
  AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/- Lemma 54.3.5 (1): if `d` is the largest exponent for which the extension of `I`
to the maximal-ideal blowup is contained in the `d`-th power of the exceptional ideal,
then `d` is positive. -/
@[stacks 0AGT] #check
  (AlgebraicGeometry.IsBlowup.maximalExceptionalPowerExponent_pos :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d),
    0 < d)

/- Lemma 54.3.5 (2): if the residual ideal `I' = I𝒪_X(dE)` is represented by
`I𝒪_X = 𝒪_X(-dE) * I'`, then `𝒪_X / I'` is supported at finitely many closed points. -/
@[stacks 0AGT] #check
  (AlgebraicGeometry.IsBlowup.residualIdealQuotient_hasFiniteClosedSupport :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d)
    (I' : X.IdealSheafData)
    (h_residual : (Scheme.idealSheafDataOfIdealOnSpec I).comap f =
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d * I'),
    ∃ (r : ℕ) (x : Fin r ↪ X),
      (∀ i, x i ∈ closedPoints X) ∧
        RingedSpace.moduleSupport (cokernel I'.toSubobject.arrow) = Set.range x)

/- Lemma 54.3.5 (3): for the residual factor `I' = I𝒪_X(dE)`, the `A`-module length
of `A ⧸ I` is strictly larger than the length of `Γ(X, 𝒪_X / I')`. -/
@[stacks 0AGT] #check
  (AlgebraicGeometry.IsBlowup.length_quotient_gt_residualIdealCohomology :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d)
    (I' : X.IdealSheafData)
    (h_residual : (Scheme.idealSheafDataOfIdealOnSpec I).comap f =
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d * I'),
    Module.length A (A ⧸ I) >
      Module.length A (Scheme.Hom.cohomology f (cokernel I'.toSubobject.arrow) 0))

/- Lemma 54.3.5 (4): for any enumeration of the closed support points of
`𝒪_X / I'`, its global `A`-module length bounds below the sum of its stalk lengths. -/
@[stacks 0AGT] #check
  (AlgebraicGeometry.IsBlowup.sum_stalkLengths_le_residualIdealCohomologyLength :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d)
    (I' : X.IdealSheafData)
    (h_residual : (Scheme.idealSheafDataOfIdealOnSpec I).comap f =
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d * I')
    (r : ℕ) (x : Fin r ↪ X) (h_closed : ∀ i, x i ∈ closedPoints X)
    (h_support : RingedSpace.moduleSupport (cokernel I'.toSubobject.arrow) = Set.range x),
    Module.length A (Scheme.Hom.cohomology f (cokernel I'.toSubobject.arrow) 0) ≥
      ∑ i, Module.length (X.presheaf.stalk (x i))
        (stalkQuotient I'.toSubobject (x i)))

end AlgebraicGeometry.IsBlowup
