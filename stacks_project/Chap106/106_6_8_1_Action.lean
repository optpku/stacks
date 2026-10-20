/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Diagonal

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

/- 106.6.8.1: Diagonal perturbation and ordered difference give the
identity-chart parameter correspondence. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.parameterIdentitySectionEquiv :
  ∀ {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
    (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
    (Δ' : U' ⟶ I') (Δ : U ⟶ I)
    [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]
    (hΔ : IsPullback Δ iU iI Δ') (hp : IsPullback p iI iU p')
    (hsec : Δ' ≫ p' = 𝟙 U'),
    ((Modules.pullback Δ).obj (Hom.relativeDifferentials p) ⟶ Hom.conormalSheaf iU) ≃
      Hom.Deformation.IdentitySection iU iI p' Δ)
