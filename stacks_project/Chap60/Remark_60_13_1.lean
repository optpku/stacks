/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_13_1_SquareZero
public import stacks_project.Chap60.Remark_60_13_1_Crystalline
public import ReasLib.AlgebraicGeometry.Crystalline.FirstOrder
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.IsFirstOrderThickening
open CrystallineObject
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineObject.FirstOrderThickening

/-- Remark 60.13.1 (1): the explicit object `(U, T', δ')` of `Cris(X/S)` whose structure
sheaf is `𝒪_T ⊕ Ω[T/S]` with square-zero multiplication.
Superseded by the divided-power construction in
`ReasLib/AlgebraicGeometry/Crystalline/FirstOrder.lean`, to be migrated and removed by 07J3 / 07J6. -/
def object
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    smallCrystallineSite S I γ h_compatible X x₀ :=
  smallObject I γ h_compatible x₀ T

/-- Remark 60.13.1 (2): the crystalline inclusion `i : T ⟶ T'`.
Superseded by the divided-power construction in
`ReasLib/AlgebraicGeometry/Crystalline/FirstOrder.lean`, to be migrated and removed by 07J3 / 07J6. -/
def inclusion
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T ⟶ object I γ h_compatible x₀ T :=
  inclusionMorph I γ h_compatible x₀ T

/-- Remark 60.13.1 (3): the crystalline retraction induced by `f ↦ (f, 0)`.
Superseded by the divided-power construction in
`ReasLib/AlgebraicGeometry/Crystalline/FirstOrder.lean`, to be migrated and removed by 07J3 / 07J6. -/
def p₀
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ T :=
  p₀Morph I γ h_compatible x₀ T

/-- Remark 60.13.1 (4): the crystalline retraction induced by `f ↦ (f, d[T/S](f))`.
Superseded by the divided-power construction in
`ReasLib/AlgebraicGeometry/Crystalline/FirstOrder.lean`, to be migrated and removed by 07J3 / 07J6. -/
def p₁
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    object I γ h_compatible x₀ T ⟶ T :=
  p₁Morph I γ h_compatible x₀ T

end CrystallineObject.FirstOrderThickening

/- Remark 60.13.1. The first-order crystalline thickening by divided-power differentials. -/
@[stacks 07J2] #check (CrystallineObject.DividedPowerFirstOrderThickening.object :
  ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀),
    smallCrystallineSite S I γ h_compatible X x₀)

variable {S : Scheme.{u}} (I : S.IdealSheafData)
  (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
  (h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
  {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
  (T : smallCrystallineSite S I γ h_compatible X x₀)

#check (CrystallineObject.DividedPowerFirstOrderThickening.inclusion I γ h_compatible x₀ T :
  T ⟶ CrystallineObject.DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T)

#check (CrystallineObject.DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T :
  CrystallineObject.DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T ⟶ T)

#check (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T :
  CrystallineObject.DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T ⟶ T)

#check (CrystallineObject.DividedPowerFirstOrderThickening.isFirstOrder I γ h_compatible x₀ T :
  IsFirstOrderThickening (CrystallineObject.DividedPowerFirstOrderThickening.inclusion I γ h_compatible x₀ T).hom.thickening)

#check (CrystallineObject.DividedPowerFirstOrderThickening.p₀_comp_inclusion I γ h_compatible x₀ T :
  CrystallineObject.DividedPowerFirstOrderThickening.inclusion I γ h_compatible x₀ T ≫ CrystallineObject.DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T = 𝟙 T)

#check (CrystallineObject.DividedPowerFirstOrderThickening.p₁_comp_inclusion I γ h_compatible x₀ T :
  CrystallineObject.DividedPowerFirstOrderThickening.inclusion I γ h_compatible x₀ T ≫ CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T = 𝟙 T)

#check (CrystallineObject.DividedPowerFirstOrderThickening.kernelIso T :
  (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module ≅
    Scheme.SquareZeroExtension.kernelModule (CrystallineObject.DividedPowerFirstOrderThickening.sheaf T) (CrystallineObject.DividedPowerFirstOrderThickening.projection T)
      (CrystallineObject.DividedPowerFirstOrderThickening.projection_isSquareZero T))

#check (CrystallineObject.DividedPowerFirstOrderThickening.ideal_eq T :
  ∀ (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) (z : (CrystallineObject.DividedPowerFirstOrderThickening.sheaf T).obj.obj V),
    z ∈ KernelIdeal.sectionIdeal (CrystallineObject.DividedPowerFirstOrderThickening.projection T) V ↔ z.1 = 0)

#check (CrystallineObject.DividedPowerFirstOrderThickening.p₁_sub_p₀ T :
  ∀ (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) (a : T.obj.1.thickening.presheaf.obj V),
    (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T).hom.app V a - (CrystallineObject.DividedPowerFirstOrderThickening.zeroLift T).hom.app V a =
      (0, (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).quotient.val.app V
        (((d[T.obj.1.thickeningToBase.toShHom]).app V).d a)))

set_option backward.isDefEq.respectTransparency false in
#check (CrystallineObject.DividedPowerFirstOrderThickening.dividedPowers_apply T :
  ∀ (V : (CrystallineObject.DividedPowerFirstOrderThickening.scheme T).affineOpens) (n : ℕ+) (z : (CrystallineObject.DividedPowerFirstOrderThickening.ideal T).ideal V),
    (CrystallineObject.DividedPowerFirstOrderThickening.dividedPowers T V).dpow n z.1 =
      ((T.obj.1.gamma (CrystallineObject.DividedPowerFirstOrderThickening.baseAffineOpen T V)).dpow n z.1.1,
        (T.obj.1.gamma (CrystallineObject.DividedPowerFirstOrderThickening.baseAffineOpen T V)).dpow ((n : ℕ) - 1) z.1.1 • z.1.2))

#check (CrystallineObject.DividedPowerFirstOrderThickening.sheaf_apply T :
  ∀ (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) (z : (CrystallineObject.DividedPowerFirstOrderThickening.sheaf T).obj.obj V),
    z = (z.1, z.2))

#check (CrystallineObject.DividedPowerFirstOrderThickening.mem_ideal_iff T :
  ∀ (V : (CrystallineObject.DividedPowerFirstOrderThickening.scheme T).affineOpens) (z : Γ(CrystallineObject.DividedPowerFirstOrderThickening.scheme T, V)),
    z ∈ (CrystallineObject.DividedPowerFirstOrderThickening.ideal T).ideal V ↔ z.1 ∈ T.obj.1.ideal.ideal (CrystallineObject.DividedPowerFirstOrderThickening.baseAffineOpen T V))
