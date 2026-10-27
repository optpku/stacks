/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.QuasiCompactImmersion

/-! # Quasi-compact immersions of functors on schemes over an algebraic space -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactOnSchemesOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isQuasiCompactOnSchemesOver_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G),
    IsQuasiCompactOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.QuasiCompact snd.left.left)

#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactImmersionOnSchemesOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isQuasiCompactImmersionOnSchemesOver_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G),
    IsQuasiCompactImmersionOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.QuasiCompact snd.left.left ∧
              AlgebraicGeometry.IsImmersion snd.left.left)

#check (AlgebraicGeometry.AlgebraicSpace.isQuasiCompactImmersionOnSchemesOver_iff_and :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G),
    IsQuasiCompactImmersionOnSchemesOver φ ↔
      IsQuasiCompactOnSchemesOver φ ∧ IsImmersionOnSchemesOver φ)
