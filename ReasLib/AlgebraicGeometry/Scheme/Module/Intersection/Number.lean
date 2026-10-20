/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Integer
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Twist

/-!
# Intersection numbers of invertible modules

This leaf owns the numerical-polynomial and finite-difference definitions of
intersection numbers on closed subschemes proper over a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- The Euler characteristic of closed-subscheme tensor twists is represented by a unique
multivariable numerical polynomial. -/
theorem existsUniqueNumericalPolynomial
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)] :
    ∃! P : MvPolynomial (Fin d) ℚ,
      ∀ n : Fin d → ℤ,
        MvPolynomial.eval (fun j : Fin d ↦ (n j : ℚ)) P =
          (eulerCharacteristic k f Z L n : ℚ) := sorry

/-- The multilinear finite difference of the twist Euler characteristic of a family of
invertible modules on a closed subscheme. -/
noncomputable def finiteDifferenceNumber
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)] : ℚ :=
  ((Finset.univ : Finset (Fin d)).powerset).sum fun s ↦
    ((-1 : ℚ) ^ (d - s.card)) *
      (eulerCharacteristic k f Z L (subsetExponent s) : ℚ)

/-- The intersection number of a family of invertible modules with a closed subscheme, defined
as the multilinear finite difference of its twist Euler characteristic. -/
noncomputable def number
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)] : ℚ :=
  finiteDifferenceNumber k f Z L

/-- An exact-dimension intersection number is its underlying multilinear finite difference. -/
theorem number_eq_finiteDifferenceNumber
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)] :
    number k f Z hZdim L = finiteDifferenceNumber k f Z L := rfl

/-- The intersection number of a dimension-`d` closed subscheme with `d` invertible modules
is an integer. -/
theorem number_isInteger
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)] :
    IsLocalization.IsInteger ℤ (number k f Z hZdim L) := sorry

/-- For a closed subscheme of dimension `d`, the geometric degree bound makes the coefficient
of the multilinear monomial in any numerical polynomial representing the twist Euler
characteristic equal to the corresponding intersection number. -/
theorem number_eq_coeff
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    {P : MvPolynomial (Fin d) ℚ}
    (hP :
      ∀ n : Fin d → ℤ,
        MvPolynomial.eval (fun j : Fin d ↦ (n j : ℚ)) P =
          (eulerCharacteristic k f Z L n : ℚ)) :
    number k f Z hZdim L = P.coeff (multilinearExponent d) := sorry

/-- The one-factor intersection coefficient of an invertible module with a closed subscheme,
defined as the first finite difference of its twist Euler characteristic. -/
noncomputable def lineNumber
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : X.Modules) [Invertible L] : ℚ :=
  let one : Fin 1 → ℤ := fun _ ↦ 1
  let zero : Fin 1 → ℤ := fun _ ↦ 0
  (eulerCharacteristic k f Z (fun _ ↦ L) one : ℚ) -
    eulerCharacteristic k f Z (fun _ ↦ L) zero

/-- Unfold `lineNumber` into the Euler-characteristic difference at exponents one and zero. -/
theorem lineNumber_def
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : X.Modules) [Invertible L] :
    lineNumber k f Z L =
      let one : Fin 1 → ℤ := fun _ ↦ 1
      let zero : Fin 1 → ℤ := fun _ ↦ 0
      (eulerCharacteristic k f Z (fun _ ↦ L) one : ℚ) -
        eulerCharacteristic k f Z (fun _ ↦ L) zero := rfl

/-- The self-intersection number of one invertible module with a closed subscheme. -/
noncomputable def selfNumber
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : X.Modules) [Invertible L] : ℚ :=
  number k f Z hZdim (fun _ ↦ L)

/-- The self-intersection number is the intersection number of the constant family of factors. -/
theorem selfNumber_def
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : X.Modules) [Invertible L] :
    selfNumber k f Z hZdim L = number k f Z hZdim (fun _ ↦ L) := rfl

/-- In dimension one, `lineNumber` is the self-intersection number of its single factor. -/
theorem lineNumber_eq_selfNumber_of_topologicalKrullDim_eq_one
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : X.Modules) [Invertible L]
    (hZdim : topologicalKrullDim Z.subscheme = 1) :
    lineNumber k f Z L = selfNumber k f Z hZdim L := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
