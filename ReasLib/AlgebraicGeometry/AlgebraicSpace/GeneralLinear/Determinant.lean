/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.Determinant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeneralLinear
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Determinant of the general linear algebraic space

The determinant morphism of group algebraic spaces `GLₙ,B ⟶ 𝔾ₘ,B` over an algebraic
space `B` is the base change of the scheme-level determinant `GLₙ,S ⟶ 𝔾ₘ[S]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeneralLinear.Determinant

/-- The algebraic-space map over `S` induced by the scheme-level determinant
`GLₙ,S ⟶ 𝔾ₘ[S]`. -/
def ofSchemeMap (S : Scheme.{u}) (n : ℕ) [NeZero n] :
    ofScheme S n ⟶ MultiplicativeGroup.ofScheme S :=
  AlgebraicGeometry.AlgebraicSpace.SchemeRealization.ofOverMap
    (AlgebraicGeometry.GeneralLinear.Determinant.baseChange S (ULift.{u} (Fin n))).hom.hom

/-- `ofSchemeMap S n` is `ofOverMap` of the underlying morphism of the scheme-level
determinant over `S`. -/
theorem ofSchemeMap_eq (S : Scheme.{u}) (n : ℕ) [NeZero n] :
    ofSchemeMap S n =
      AlgebraicGeometry.AlgebraicSpace.SchemeRealization.ofOverMap
        (AlgebraicGeometry.GeneralLinear.Determinant.baseChange S
          (ULift.{u} (Fin n))).hom.hom :=
  sorry

/-- The underlying algebraic-space map of the determinant over `B`, into
`𝔾ₘ,B = B ×_S 𝔾ₘ[S]`. -/
def spaceHom {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    space B n ⟶ MultiplicativeGroup.space B :=
  Limits.prod.lift (X := B.functorOfPoints)
    (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.hom B n)
    ((Limits.prod.snd :
        (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶
          (ofScheme S n).functorOfPoints) ≫ ofSchemeMap S n)

/-- `spaceHom B n` is the product lift of the structure morphism of `GLₙ,B` with the
scheme-level determinant on the `GLₙ,S` factor. -/
theorem spaceHom_eq {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    spaceHom B n =
      Limits.prod.lift (X := B.functorOfPoints)
        (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.hom B n)
        ((Limits.prod.snd :
            (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶
              (ofScheme S n).functorOfPoints) ≫ ofSchemeMap S n) :=
  sorry

/-- `spaceHom B n` is a morphism over `B`. -/
theorem spaceHom_fst {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    spaceHom B n ≫ MultiplicativeGroup.hom B =
      AlgebraicGeometry.AlgebraicSpace.GeneralLinear.hom B n :=
  sorry

/-- The determinant as a morphism of algebraic spaces over `B`. -/
def overHom {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    asOver B n ⟶ MultiplicativeGroup.asOver B :=
  Over.homMk (spaceHom B n) (spaceHom_fst B n)

/-- The underlying algebraic-space map of `overHom` is `spaceHom`. -/
theorem overHom_left {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (overHom B n).left = spaceHom B n :=
  sorry

/-- The determinant over `B` preserves units of the group algebraic spaces. -/
theorem overHom_one {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    η ≫ overHom B n = η :=
  sorry

/-- The determinant over `B` preserves multiplication of the group algebraic spaces. -/
theorem overHom_mul {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    μ ≫ overHom B n = (overHom B n ⊗ₘ overHom B n) ≫ μ :=
  sorry

/-- The determinant morphism of group algebraic spaces `GLₙ,B ⟶ 𝔾ₘ,B` over `B`,
obtained as the base change of the scheme-level determinant over `S`. -/
def hom {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    groupSpace B n ⟶ MultiplicativeGroup.groupSpace B :=
  Grp.homMk'' (overHom B n) (overHom_one B n) (overHom_mul B n)

/-- The underlying slice morphism of `hom` is `overHom`. -/
theorem hom_hom_hom {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (hom B n).hom.hom = overHom B n :=
  sorry

/-- The underlying algebraic-space map of `hom B n` is the product-lift base change of
the scheme-level determinant. -/
theorem hom_left {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (hom B n).hom.hom.left =
      Limits.prod.lift (X := B.functorOfPoints)
        (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.hom B n)
        ((Limits.prod.snd :
            (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶
              (ofScheme S n).functorOfPoints) ≫ ofSchemeMap S n) :=
  sorry

/-- On scheme-valued points over `B`, `hom B n` is the matrix determinant. -/
theorem hom_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B) (f : Over.mk t ⟶ asOver B n) :
    MultiplicativeGroup.homOverMulEquiv t (f ≫ (hom B n).hom.hom) =
      Matrix.GeneralLinearGroup.det (homOverMulEquiv n t f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeneralLinear.Determinant
