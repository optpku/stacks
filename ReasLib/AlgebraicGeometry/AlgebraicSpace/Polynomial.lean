/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Polynomial affine-space objects over an algebraic space

A polynomial affine-space object consists of a scheme étale over an algebraic space,
together with a morphism to affine space commuting with the maps to the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Polynomial

variable (R : CommRingCat.{u}) (X : AlgebraicSpace (Spec R))

/-- A scheme `U` étale over the algebraic space `X` over `Spec R`, together with a morphism
`U.left ⟶ 𝔸(vars; Spec R)` commuting with the structure morphisms to `Spec R`. -/
structure Object where
  /-- The scheme over `Spec R`. -/
  U : Over (Spec R)
  /-- The index type of affine-space coordinates. -/
  vars : Type u
  /-- The morphism from the scheme, viewed as an algebraic space, to `X`. -/
  toSpace : ofOver U ⟶ X
  /-- The morphism `toSpace` is étale. -/
  etale : Etale toSpace
  /-- The morphism from the scheme to affine space over `Spec R`. -/
  toAffine : U.left ⟶ 𝔸(vars; Spec R)
  /-- The square `U.left ⟶ 𝔸(vars; Spec R)` over `Spec R` commutes. -/
  w : toAffine ≫ (𝔸(vars; Spec R) ↘ Spec R) = U.hom

namespace Object

variable {R X}

/-- Construct a polynomial affine-space object from a scheme étale over `X` and a morphism
to affine space commuting with the structure morphisms to `Spec R`. -/
def of (U : Over (Spec R)) (toSpace : ofOver U ⟶ X) (etale : Etale toSpace)
    (vars : Type u) (toAffine : U.left ⟶ 𝔸(vars; Spec R))
    (w : toAffine ≫ (𝔸(vars; Spec R) ↘ Spec R) = U.hom) : Object R X where
  U := U
  vars := vars
  toSpace := toSpace
  etale := etale
  toAffine := toAffine
  w := w

/-- Construct a polynomial affine-space object from an étale morphism to `X` and a family
of global sections of its domain. -/
def ofVector {U : Over (Spec R)} (toSpace : ofOver U ⟶ X) [Etale toSpace]
    (ι : Type u) (v : ι → Γ(U.left, ⊤)) : Object R X where
  U := U
  vars := ι
  toSpace := toSpace
  etale := ‹Etale toSpace›
  toAffine := AffineSpace.homOfVector U.hom v
  w := AffineSpace.homOfVector_over U.hom v

/-- The scheme of `ofVector toSpace ι v` is the domain of `toSpace`. -/
theorem ofVector_U {U : Over (Spec R)} (toSpace : ofOver U ⟶ X) [Etale toSpace]
    (ι : Type u) (v : ι → Γ(U.left, ⊤)) :
    (ofVector toSpace ι v).U = U := sorry

/-- The variable type of `ofVector toSpace ι v` is `ι`. -/
theorem ofVector_vars {U : Over (Spec R)} (toSpace : ofOver U ⟶ X) [Etale toSpace]
    (ι : Type u) (v : ι → Γ(U.left, ⊤)) :
    (ofVector toSpace ι v).vars = ι := sorry

/-- The affine-space morphism of `ofVector toSpace ι v` is `AffineSpace.homOfVector`. -/
theorem ofVector_toAffine {U : Over (Spec R)} (toSpace : ofOver U ⟶ X) [Etale toSpace]
    (ι : Type u) (v : ι → Γ(U.left, ⊤)) :
    (ofVector toSpace ι v).toAffine = AffineSpace.homOfVector U.hom v := sorry

/-- The morphism to `X` of `ofVector toSpace ι v` is `toSpace`. -/
theorem ofVector_toSpace {U : Over (Spec R)} (toSpace : ofOver U ⟶ X) [Etale toSpace]
    (ι : Type u) (v : ι → Γ(U.left, ⊤)) :
    (ofVector toSpace ι v).toSpace = toSpace := sorry

/-- The affine-space vertex of the object square. -/
abbrev A (obj : Object R X) : Scheme.{u} := 𝔸(obj.vars; Spec R)

/-- The structure morphism of the affine-space vertex over `Spec R`. -/
abbrev toBase (obj : Object R X) : 𝔸(obj.vars; Spec R) ⟶ Spec R :=
  𝔸(obj.vars; Spec R) ↘ Spec R

/-- The commutative square `U.left ⟶ 𝔸(obj.vars; Spec R)` over `Spec R`. -/
theorem commSq (obj : Object R X) :
    CommSq obj.toAffine obj.U.hom obj.toBase (𝟙 (Spec R)) :=
  ⟨obj.w⟩

/-- Affine space over `Spec R` is isomorphic to the spectrum of the polynomial `R`-algebra
on `obj.vars`. -/
def specIso (obj : Object R X) :
    𝔸(obj.vars; Spec R) ≅ Spec (.of (MvPolynomial obj.vars R)) :=
  AffineSpace.SpecIso obj.vars R

/-- A polynomial affine-space object has an étale morphism to `X`, a commuting square over
`Spec R`, and an affine-space vertex isomorphic to the spectrum of a polynomial `R`-algebra. -/
theorem spec (obj : Object R X) :
    Etale obj.toSpace ∧
      (obj.toAffine ≫ obj.toBase = obj.U.hom) ∧
      Nonempty (𝔸(obj.vars; Spec R) ≅ Spec (.of (MvPolynomial obj.vars R))) := sorry

end Object

end AlgebraicGeometry.AlgebraicSpace.Polynomial
