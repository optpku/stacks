/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Affine-space presentations of varieties

This leaf owns the explicit closed-immersion presentation of a variety into an
affine space over its base field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k]

/-- The affine `n`-space over the field `k`. -/
noncomputable abbrev AffineSpaceOverField (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k))

/-- The structure morphism from affine `n`-space over `k` to `Spec k`. -/
noncomputable abbrev affineSpaceOverFieldHom (k : Type u) [Field k] (n : ℕ) :
    AffineSpaceOverField k n ⟶ Spec (CommRingCat.of.{u} k) :=
  AffineSpaceOverField k n ↘ Spec (CommRingCat.of.{u} k)

/-- `IsAffineSpacePresentation X n i` means that `i` is a closed immersion from `X` into affine
`n`-space over `k` and commutes with the structure morphisms to `Spec k`. -/
def IsAffineSpacePresentation
    (X : SchemeOverField k) (n : ℕ) (i : X.left ⟶ AffineSpaceOverField k n) : Prop :=
  IsClosedImmersion i ∧ i ≫ affineSpaceOverFieldHom k n = X.hom

/-- Expand `IsAffineSpacePresentation X n i` into the closed-immersion and base-compatibility
conditions. -/
theorem isAffineSpacePresentation_iff
    (X : SchemeOverField k) (n : ℕ) (i : X.left ⟶ AffineSpaceOverField k n) :
    IsAffineSpacePresentation X n i ↔
      IsClosedImmersion i ∧ i ≫ affineSpaceOverFieldHom k n = X.hom := sorry

/-- `X` admits a closed-immersion presentation into some affine space over `Spec k`. -/
def HasAffineSpacePresentation (X : SchemeOverField k) : Prop :=
  ∃ n : ℕ, ∃ i : X.left ⟶ AffineSpaceOverField k n, IsAffineSpacePresentation X n i

/-- Expand `HasAffineSpacePresentation X` into a choice of affine-space dimension and
closed-immersion presentation. -/
theorem hasAffineSpacePresentation_iff (X : SchemeOverField k) :
    HasAffineSpacePresentation X ↔
      ∃ n : ℕ, ∃ i : X.left ⟶ AffineSpaceOverField k n,
        IsAffineSpacePresentation X n i := sorry

/-- A variety over `k` is affine exactly when it admits a closed-immersion presentation into some
affine space over `Spec k`. -/
theorem affineVariety_iff_hasAffineSpacePresentation
    (X : SchemeOverField k) [Variety X] :
    AffineVariety X ↔ HasAffineSpacePresentation X := sorry

end

end AlgebraicGeometry
