/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Automorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

/- 106.6.8.1: Acting on the supplied diagonal identifies the sheaf of
`O_U`-linear maps from `Δ^* Ω_{I/U}` to `C_{U/U'}` with the automorphism
sections of the first-order cartesian diagram. -/
@[stacks 0CKH] #check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.parameterAutIso :
  ∀ {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
    (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
    (Δ' : U' ⟶ I') (Δ : U ⟶ I)
    [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]
    (hΔ : IsPullback Δ iU iI Δ') (hp : IsPullback p iI iU p')
    (hsec : Δ' ≫ p' = 𝟙 U'),
    Hom.Deformation.parameterSheafEtale iU p Δ ≅
      Hom.Deformation.autSheaf iU iI p' Δ' Δ hΔ)
