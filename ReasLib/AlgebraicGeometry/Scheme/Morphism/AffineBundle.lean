/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Geometric properties of affine-space bundles

Morphisms locally isomorphic over their target to finite-dimensional relative affine space
are flat and have the corresponding relative dimension.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism locally isomorphic over its target to relative affine space is flat. -/
theorem flat_of_localAffineSpace {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h_local : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      Nonempty (Over.mk (f ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme))) :
    Flat f := sorry

/-- A morphism locally isomorphic over its target to relative affine `r`-space is locally
of finite type and has relative dimension `r`. -/
theorem relativeDimension_of_localAffineSpace {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h_local : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      Nonempty (Over.mk (f ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme))) :
    RelativeDimension f r := sorry

/-- The source of an affine-space bundle over a scheme locally of finite type over a base
is locally of finite type over that base. -/
theorem locallyOfFiniteType_over_of_localAffineSpace {S : Scheme.{u}}
    (X Y : Over S) [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) (r : ℕ)
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme))) :
    LocallyOfFiniteType X.hom := by
  have hcomp : LocallyOfFiniteType (f.left ≫ Y.hom) :=
    @locallyOfFiniteType_comp _ _ _ f.left Y.hom
      (relativeDimension_of_localAffineSpace f.left r h_local).toLocallyOfFiniteType
      inferInstance
  rwa [Over.w f] at hcomp

end AlgebraicGeometry.Scheme.Hom
