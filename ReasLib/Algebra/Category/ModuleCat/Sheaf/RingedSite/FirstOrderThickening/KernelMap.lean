/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The underlying additive sheaf map of an 𝒪-module morphism landing in a restriction of
scalars. -/
def toAdditive {O O' : Sheaf J CommRingCat.{max u v}} (α : O ⟶ O')
    {M : SheafOfModules (ringSheaf J O)} {N : SheafOfModules (ringSheaf J O')}
    (φ : M ⟶ (restrictionAlong α).obj N) :
    (SheafOfModules.toSheaf (ringSheaf J O)).obj M ⟶
      (SheafOfModules.toSheaf (ringSheaf J O')).obj N :=
  (SheafOfModules.toSheaf (ringSheaf J O)).map φ ≫
    (SheafOfModules.restrictScalarsCompToSheaf (ringSheafMap α)).hom.app N

variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}

/-- The composite of the kernel inclusion of `πB` with the additive map of `f'` is killed by
the projection of `πO`. -/
theorem inducedKernelMap_lift_zero (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O)
    (f' : OB' ⟶ O') [IsFirstOrderThickening πB] [IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    (kernel.ι (KernelIdeal.underlyingProjection πB) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap f')) ≫
      KernelIdeal.underlyingProjection πO = 0 := sorry

/-- The additive sheaf map of kernel ideals induced by a commutative square of ring sheaves. -/
def inducedKernelAdditiveMap (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O) (f' : OB' ⟶ O')
    [hπB : IsFirstOrderThickening πB] [hπO : IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    (SheafOfModules.toSheaf (ringSheaf J OB)).obj (ideal πB) ⟶
      (SheafOfModules.toSheaf (ringSheaf J O)).obj (ideal πO) :=
  (hπB.isSquareZero.targetModuleForgetIso inferInstance).hom ≫
    (KernelIdeal.underlyingKernelIso πB).hom ≫
      kernel.lift (KernelIdeal.underlyingProjection πO)
        (kernel.ι (KernelIdeal.underlyingProjection πB) ≫
          SheafOfModules.unitUnderlyingMap (ringSheafMap f'))
        (inducedKernelMap_lift_zero πB f πO f' hcomm) ≫
      (KernelIdeal.underlyingKernelIso πO).inv ≫
        (hπO.isSquareZero.targetModuleForgetIso inferInstance).inv

/-- The additive kernel comparison is linear over the source quotient ring sheaf. -/
theorem inducedKernelMap_smul (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O)
    (f' : OB' ⟶ O') [IsFirstOrderThickening πB] [IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) (U : Cᵒᵖ)
    (r : (ringSheaf J OB).obj.obj U) (m : (ideal πB).val.obj U) :
    (inducedKernelAdditiveMap πB f πO f' hcomm).hom.app U
        (((ideal πB).val.obj U).isModule.smul r m) =
      (((restrictionAlong f).obj (ideal πO)).val.obj U).isModule.smul r
        ((inducedKernelAdditiveMap πB f πO f' hcomm).hom.app U m) := sorry

/-- The 𝒪_B-module map on kernel ideals induced by a commutative square of ring sheaves. -/
def inducedKernelMap (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O) (f' : OB' ⟶ O')
    [IsFirstOrderThickening πB] [IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    ideal πB ⟶ (restrictionAlong f).obj (ideal πO) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).map
        (inducedKernelAdditiveMap πB f πO f' hcomm))
      (inducedKernelMap_smul πB f πO f' hcomm)

/-- Forgetting `inducedKernelMap` to additive sheaves recovers `inducedKernelAdditiveMap`. -/
theorem inducedKernelMap_toAdditive (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O)
    (f' : OB' ⟶ O') [IsFirstOrderThickening πB] [IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    toAdditive f (inducedKernelMap πB f πO f' hcomm) =
      inducedKernelAdditiveMap πB f πO f' hcomm := sorry

/-- Additive kernel maps of composable commutative squares compose. -/
theorem inducedKernelMap_comp_toAdditive
    {O1' O1 O2' O2 O3' O3 : Sheaf J CommRingCat.{max u v}}
    (π1 : O1' ⟶ O1) (π2 : O2' ⟶ O2) (π3 : O3' ⟶ O3)
    [IsFirstOrderThickening π1] [IsFirstOrderThickening π2] [IsFirstOrderThickening π3]
    (f12 : O1 ⟶ O2) (f23 : O2 ⟶ O3) (f12' : O1' ⟶ O2') (f23' : O2' ⟶ O3')
    (h12 : f12' ≫ π2 = π1 ≫ f12) (h23 : f23' ≫ π3 = π2 ≫ f23)
    (h13 : (f12' ≫ f23') ≫ π3 = π1 ≫ f12 ≫ f23) :
    toAdditive (f12 ≫ f23) (inducedKernelMap π1 (f12 ≫ f23) π3 (f12' ≫ f23') h13) =
      toAdditive f12 (inducedKernelMap π1 f12 π2 f12' h12) ≫
        toAdditive f23 (inducedKernelMap π2 f23 π3 f23' h23) := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
