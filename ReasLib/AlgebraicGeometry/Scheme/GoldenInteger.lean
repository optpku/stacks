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

/-- The explicit unit with value `evalAtCoord denom` and inverse `(φ - 1) ^ 6`. -/
def denomUnit : Orderˣ where
  val := evalAtCoord denom
  inv := (phi - 1) ^ 6
  val_inv := sorry
  inv_val := sorry

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
    coordinateRingHom (algebraMap ℤ[X] CoordinateRing X) = coord := sorry

/-- The structure morphism of `scheme` factors as the closed immersion
followed by the structure morphism of `ambient`. -/
theorem toSpecInt_eq_comp :
    toSpecInt = closedImmersion ≫ ambientToSpecInt := sorry

/-- `closedImmersion` is a closed immersion. -/
instance instIsClosedImmersion : IsClosedImmersion closedImmersion := sorry

/-- The structure morphism `toSpecInt` is finite. -/
instance instIsFinite_toSpecInt : IsFinite toSpecInt := sorry

/-- The structure morphism `toSpecInt` is surjective. -/
instance instSurjective_toSpecInt : Surjective toSpecInt := sorry

end AlgebraicGeometry.GoldenIntegerQuasiSection
