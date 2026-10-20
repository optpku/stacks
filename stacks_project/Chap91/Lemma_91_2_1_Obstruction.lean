/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.Obstruction

/-! The shared obstruction API used by the source-facing item. -/

@[expose] public section

universe u

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent :
  (A B N : Type u) → [CommRing A] → [CommRing B] → [Algebra A B] →
    [AddCommGroup N] → [Module B N] → Type u)
#check (RingHom.SquareZeroExtension.liftPoly :
  ∀ {A₁' A₁ B₁ : Type u} [CommRing A₁'] [CommRing A₁]
    (π : A₁' →+* A₁) [π.IsSquareZeroExtension],
    MvPolynomial B₁ A₁ → MvPolynomial B₁ A₁')
#check (RingHom.SquareZeroExtension.RelativeDiagram.mapObstruction :
  ∀ {A₁' A₁ B₁ N₁ A₂' A₂ B₂ N₂ : Type u} [CommRing A₁'] [CommRing A₁]
    [CommRing B₁] [Algebra A₁ B₁] [CommRing A₂'] [CommRing A₂] [CommRing B₂]
    [Algebra A₂ B₂] [AddCommGroup N₁] [Module B₁ N₁] [Module A₁ N₁]
    [IsScalarTower A₁ B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂] [Module A₂ N₂]
    [IsScalarTower A₂ B₂ N₂] {π₁ : A₁' →+* A₁} [π₁.IsSquareZeroExtension]
    {π₂ : A₂' →+* A₂} [π₂.IsSquareZeroExtension]
    {c₁ : RingHom.SquareZeroExtension.KernelModule π₁ →ₗ[A₁] N₁}
    {c₂ : RingHom.SquareZeroExtension.KernelModule π₂ →ₗ[A₂] N₂}
    {S₁ : RingHom.SquareZeroExtension.Solution π₁ c₁}
    {S₂ : RingHom.SquareZeroExtension.Solution π₂ c₂}
    (D : RingHom.SquareZeroExtension.RelativeDiagram S₁ S₂),
    RingHom.SquareZeroExtension.RelativeDiagram.ObstructionGroup D)
