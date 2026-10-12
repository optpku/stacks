/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

variable {k : Type u} [Field k] {n : ℕ}

/-- The endomorphism of affine space sending coordinate `i` to
`x_i + x_j ^ d` and fixing every other coordinate. -/
def elementaryShearHom (i j : Fin n) (d : ℕ) :
    𝔸(ULift.{u} (Fin n); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k)) :=
  homOfVector (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) fun l ↦
    if l = ULift.up i then
      coord (Spec (.of k)) (ULift.up i) + coord (Spec (.of k)) (ULift.up j) ^ d
    else coord (Spec (.of k)) l

/-- The endomorphism inverse to `elementaryShearHom` when `i ≠ j`, obtained by
subtracting `x_j ^ d` from coordinate `i`. -/
def elementaryShearInvHom (i j : Fin n) (d : ℕ) :
    𝔸(ULift.{u} (Fin n); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k)) :=
  homOfVector (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) fun l ↦
    if l = ULift.up i then
      coord (Spec (.of k)) (ULift.up i) - coord (Spec (.of k)) (ULift.up j) ^ d
    else coord (Spec (.of k)) l

/-- Composing an elementary shear with its subtraction shear is the identity. -/
theorem elementaryShearHom_comp_invHom (i j : Fin n) (hij : i ≠ j) (d : ℕ) :
    (elementaryShearHom i j d :
        𝔸(ULift.{u} (Fin n); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k))) ≫
      elementaryShearInvHom i j d = 𝟙 _ := sorry

/-- Composing the subtraction shear with its elementary shear is the identity. -/
theorem elementaryShearInvHom_comp_hom (i j : Fin n) (hij : i ≠ j) (d : ℕ) :
    (elementaryShearInvHom i j d :
        𝔸(ULift.{u} (Fin n); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k))) ≫
      elementaryShearHom i j d = 𝟙 _ := sorry

/-- The affine-space automorphism which adds `x_j ^ d` to `x_i`. -/
def elementaryShear (i j : Fin n) (hij : i ≠ j) (d : ℕ) :
    𝔸(ULift.{u} (Fin n); Spec (.of k)) ≅ 𝔸(ULift.{u} (Fin n); Spec (.of k)) where
  hom := elementaryShearHom i j d
  inv := elementaryShearInvHom i j d
  hom_inv_id := elementaryShearHom_comp_invHom i j hij d
  inv_hom_id := elementaryShearInvHom_comp_hom i j hij d

/-- Pullback by `elementaryShear` has the prescribed effect on every affine coordinate. -/
theorem elementaryShear_appTop_coord (i j : Fin n) (hij : i ≠ j) (d : ℕ)
    (l : Fin n) :
    (elementaryShear i j hij d).hom.appTop (coord (Spec (.of k)) (ULift.up l)) =
      if l = i then
        coord (Spec (.of k)) (ULift.up i) + coord (Spec (.of k)) (ULift.up j) ^ d
      else coord (Spec (.of k)) (ULift.up l) := sorry

end AlgebraicGeometry.AffineSpace
