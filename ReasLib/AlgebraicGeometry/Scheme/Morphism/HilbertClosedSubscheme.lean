/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Closed subschemes of bounded relative dimension

This file packages closed subschemes whose structure morphisms are flat, of
finite presentation, and of bounded relative dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- A closed subscheme of `X` whose structure morphism to `S` is flat, of finite
presentation, and of relative dimension at most `r`. -/
structure HilbertClosedSubscheme (f : X ⟶ S) (r : ℕ) : Type u where
  /-- The ideal sheaf of the closed subscheme `Z ⊂ X`. -/
  ideal : X.IdealSheafData
  /-- The structure morphism `Z ⟶ S` is flat. -/
  flat : Flat (ideal.subschemeι ≫ f)
  /-- The structure morphism `Z ⟶ S` is of finite presentation. -/
  finitePresentation : FinitePresentation (ideal.subschemeι ≫ f)
  /-- The structure morphism `Z ⟶ S` has relative dimension at most `r`. -/
  relativeDimensionLE : RelativeDimensionLE (ideal.subschemeι ≫ f) r

namespace HilbertClosedSubscheme

/-- Package a closed subscheme of `X` whose structure morphism to `S` is flat, of
finite presentation, and of relative dimension at most `r`. -/
def ofIdeal {f : X ⟶ S} {r : ℕ} (Z : X.IdealSheafData)
    (hflat : Flat (Z.subschemeι ≫ f))
    (hfp : FinitePresentation (Z.subschemeι ≫ f))
    (hdim : RelativeDimensionLE (Z.subschemeι ≫ f) r) :
    HilbertClosedSubscheme f r where
  ideal := Z
  flat := hflat
  finitePresentation := hfp
  relativeDimensionLE := hdim

/-- `ofIdeal` retains the given ideal sheaf. -/
theorem ideal_ofIdeal {f : X ⟶ S} {r : ℕ} (Z : X.IdealSheafData)
    (hflat : Flat (Z.subschemeι ≫ f))
    (hfp : FinitePresentation (Z.subschemeι ≫ f))
    (hdim : RelativeDimensionLE (Z.subschemeι ≫ f) r) :
    (ofIdeal Z hflat hfp hdim).ideal = Z := sorry

/-- Membership in `Hilb(X/S, r)` is flatness, finite presentation, and relative
dimension at most `r` for `Z ⟶ S`. -/
theorem spec {f : X ⟶ S} {r : ℕ} (Z : HilbertClosedSubscheme f r) :
    Flat (Z.ideal.subschemeι ≫ f) ∧
      FinitePresentation (Z.ideal.subschemeι ≫ f) ∧
      RelativeDimensionLE (Z.ideal.subschemeι ≫ f) r := sorry

end HilbertClosedSubscheme

/-- Unbundled recognition of a closed subscheme of `X` as an element of
`Hilb(X/S, r)`. -/
def IsHilbertClosedSubscheme (f : X ⟶ S) (r : ℕ) (Z : X.IdealSheafData) : Prop :=
  Flat (Z.subschemeι ≫ f) ∧
    FinitePresentation (Z.subschemeι ≫ f) ∧
    RelativeDimensionLE (Z.subschemeι ≫ f) r

/-- A closed subscheme arises from `HilbertClosedSubscheme` if and only if its
structure morphism to `S` is flat, of finite presentation, and of relative
dimension at most `r`. -/
theorem isHilbertClosedSubscheme_iff (f : X ⟶ S) (r : ℕ) (Z : X.IdealSheafData) :
    (∃ Z' : HilbertClosedSubscheme f r, Z'.ideal = Z) ↔
      IsHilbertClosedSubscheme f r Z := sorry

end AlgebraicGeometry.Scheme.Hom
