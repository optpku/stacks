/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.KernelCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/-- The fibre of a smooth proper morphism over a `k`-rational section `σ : Spec k ⟶ S`,
as the pullback `Y ×_S Spec k`. -/
noncomputable def FourierMukaiObject.fiberOver
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    FourierMukaiObject (Spec (.of k)) :=
  FourierMukaiObject.mk (pullback Y.hom σ) (pullback.snd Y.hom σ)
    (MorphismProperty.pullback_snd Y.hom σ Y.smooth)
    (MorphismProperty.pullback_snd Y.hom σ Y.proper)

/-- The constant family `Y_s ×_{Spec k} S` over `S`. -/
noncomputable def FourierMukaiObject.constantFamily
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    FourierMukaiObject S :=
  FourierMukaiObject.baseChange hS (FourierMukaiObject.fiberOver hS σ hσ Y)

/-- The structure morphism of the constant family is the base-change projection to `S`. -/
theorem FourierMukaiObject.constantFamily_hom
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    (FourierMukaiObject.constantFamily hS σ hσ Y).hom =
      pullback.fst hS (FourierMukaiObject.fiberOver hS σ hσ Y).hom := rfl

/-- The fibre of the constant family at the image of `σ` is isomorphic to `Y_s`. -/
theorem FourierMukaiObject.constantFamily_fiber
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    IsIsomorphic
      ((FourierMukaiObject.constantFamily hS σ hσ Y).hom.fiber (σ (closedPoint k)))
      (pullback Y.hom σ) := sorry

/-- The first projection of `Y_s ×_k Y_s` is compatible with the pullback square
defining the constant family. -/
theorem FourierMukaiObject.fiberSquare_fst_lift_condition
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    (pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
      pullback.fst Y.hom σ ≫ Y.hom) ≫ hS =
      pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
          (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom := sorry

/-- The map `Y_s ×_k Y_s ⟶ Y_s ×_{Spec k} S` induced by the first projection. -/
noncomputable def FourierMukaiObject.fiberSquareToConstantFamily
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    pullback (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ⟶
      (FourierMukaiObject.constantFamily hS σ hσ Y).scheme :=
  pullback.lift
    (pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
      pullback.fst Y.hom σ ≫ Y.hom)
    (pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
      (FourierMukaiObject.fiberOver hS σ hσ Y).hom)
    (FourierMukaiObject.fiberSquare_fst_lift_condition hS σ hσ Y)

/-- The two legs of `Y_s ×_k Y_s ⟶ (Y_s × S) ×_S Y` agree over `S`. -/
theorem FourierMukaiObject.fiberSquareToConstantProduct_condition
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    FourierMukaiObject.fiberSquareToConstantFamily hS σ hσ Y ≫
        (FourierMukaiObject.constantFamily hS σ hσ Y).hom =
      (pullback.snd (FourierMukaiObject.fiberOver hS σ hσ Y).hom
          (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
        pullback.fst Y.hom σ) ≫ Y.hom := sorry

/-- The comparison morphism `Y_s ×_k Y_s ⟶ (Y_s × S) ×_S Y` used to restrict kernels. -/
noncomputable def FourierMukaiObject.fiberSquareToConstantProduct
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    pullback (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ⟶
      pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom :=
  pullback.lift
    (FourierMukaiObject.fiberSquareToConstantFamily hS σ hσ Y)
    (pullback.snd (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
      pullback.fst Y.hom σ)
    (FourierMukaiObject.fiberSquareToConstantProduct_condition hS σ hσ Y)

/-- Derived restriction of a perfect kernel along the fibre-square comparison. -/
noncomputable def FourierMukaiObject.fiberSquarePullbackKernel
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom).toRingedSpace :=
  (RingedSpace.modulePullbackPerfect
    (FourierMukaiObject.fiberSquareToConstantProduct hS σ hσ Y).toLRSHom.toShHom).obj K

/-- Restriction of `K` along `Y_s × Y_s ⟶ X ×_S Y` is the derived pullback of `K`. -/
theorem FourierMukaiObject.fiberSquarePullbackKernel_spec
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom).toRingedSpace) :
    FourierMukaiObject.fiberSquarePullbackKernel hS σ hσ Y K =
      (RingedSpace.modulePullbackPerfect
        (FourierMukaiObject.fiberSquareToConstantProduct hS σ hσ Y).toLRSHom.toShHom).obj K :=
  rfl
