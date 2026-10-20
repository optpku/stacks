/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.Diagram

/-! The shared relative-diagram API used by the source-facing item. -/

@[expose] public section

universe u

/- The source item retains the public names through the shared owner. -/
#check (RingHom.SquareZeroExtension.RelativeDiagram :
  ∀ {A₁' A₁ B₁ N₁ A₂' A₂ B₂ N₂ : Type u} [CommRing A₁'] [CommRing A₁]
    [CommRing B₁] [Algebra A₁ B₁] [CommRing A₂'] [CommRing A₂] [CommRing B₂]
    [Algebra A₂ B₂] [AddCommGroup N₁] [Module B₁ N₁] [Module A₁ N₁]
    [IsScalarTower A₁ B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂] [Module A₂ N₂]
    [IsScalarTower A₂ B₂ N₂] {π₁ : A₁' →+* A₁} [π₁.IsSquareZeroExtension]
    {π₂ : A₂' →+* A₂} [π₂.IsSquareZeroExtension]
    {c₁ : RingHom.SquareZeroExtension.KernelModule π₁ →ₗ[A₁] N₁}
    {c₂ : RingHom.SquareZeroExtension.KernelModule π₂ →ₗ[A₂] N₂},
    RingHom.SquareZeroExtension.Solution π₁ c₁ →
      RingHom.SquareZeroExtension.Solution π₂ c₂ → Type u)
#check (RingHom.SquareZeroExtension.FittingMap :
  ∀ {A₁' A₁ B₁ N₁ A₂' A₂ B₂ N₂ : Type u} [CommRing A₁'] [CommRing A₁]
    [CommRing B₁] [Algebra A₁ B₁] [CommRing A₂'] [CommRing A₂] [CommRing B₂]
    [Algebra A₂ B₂] [AddCommGroup N₁] [Module B₁ N₁] [Module A₁ N₁]
    [IsScalarTower A₁ B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂] [Module A₂ N₂]
    [IsScalarTower A₂ B₂ N₂] {π₁ : A₁' →+* A₁} [π₁.IsSquareZeroExtension]
    {π₂ : A₂' →+* A₂} [π₂.IsSquareZeroExtension]
    {c₁ : RingHom.SquareZeroExtension.KernelModule π₁ →ₗ[A₁] N₁}
    {c₂ : RingHom.SquareZeroExtension.KernelModule π₂ →ₗ[A₂] N₂}
    {S₁ : RingHom.SquareZeroExtension.Solution π₁ c₁}
    {S₂ : RingHom.SquareZeroExtension.Solution π₂ c₂},
    RingHom.SquareZeroExtension.RelativeDiagram S₁ S₂ → Type u)
#check (RingHom.SquareZeroExtension.FittingMap.perturb :
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
      RingHom.SquareZeroExtension.RelativeDiagram.Differentials D →
        RingHom.SquareZeroExtension.FittingMap D →
          RingHom.SquareZeroExtension.FittingMap D)
