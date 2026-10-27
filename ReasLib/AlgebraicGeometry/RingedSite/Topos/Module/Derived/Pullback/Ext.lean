/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback.CellModel
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.CellModel
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped DerivedExt
noncomputable section

universe uX vX uY vY w
namespace RingedSite.ToposHom.DerivedPullback

-- Local instance justification (defeq pin): the cell localization and the extension classification must use the same standard derived-category dictionary.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
  [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasSheafify JX AddCommGrpCat.{w}] [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JY AddCommGrpCat.{w}] [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable (g : ToposHom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY))
variable [hX : UnivLE.{max uX vX, w}] [hY : UnivLE.{max uY vY, w}]
variable [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]

/-- Pullback of the specified cell replacements inverts quasi-isomorphisms. -/
theorem invertsQuasiIso :
    (HomologicalComplex.quasiIso (ModuleCat.{w} (ofCommRingSheaf JY OY)) (up ℤ)).IsInvertedBy
      (SheafOfModules.CellReplacement.functor ⋙ g.modulePullbackComplex ⋙ (DerivedCategory.Q (C := ModuleCat.{w} (ofCommRingSheaf JX OX)))) := sorry

/-- Pullback of the augmentation of a cell model is a quasi-isomorphism. -/
theorem augmentationOnModels_quasiIso
    (K : CochainComplex (ModuleCat.{w} (ofCommRingSheaf JY OY)) ℤ) :
    QuasiIso (g.modulePullbackComplex.map
      (SheafOfModules.CellReplacement.augmentation
        (SheafOfModules.CellReplacement.model K))) := sorry

/-- Derived pullback is localization of pullback of the actual cell replacement. -/
def functor : Hom.ModuleDerived.{w} (ofCommRingSheaf JY OY) ⥤
    Hom.ModuleDerived.{w} (ofCommRingSheaf JX OX) :=
  @Functor.CellModel.derived _ _ _ _ _ _ _ _ _ _ _
      g.modulePullback (modulePullback_additive g) (invertsQuasiIso g)

/-- The derived pullback counit is induced by the specified cell augmentation. -/
def counit : DerivedCategory.Q ⋙ functor g ⟶
    (g.modulePullbackComplex ⋙ DerivedCategory.Q) :=
  @Functor.CellModel.counit _ _ _ _ _ _ _ _ _ _ _
      g.modulePullback (modulePullback_additive g) (invertsQuasiIso g)

/-- The shifted-source counit uses the canonical cochain and localization shift comparisons. -/
def shiftSourceCounit (n : ℤ) :
    DerivedCategory.Q ⋙ (shiftFunctor _ n ⋙ functor g) ⟶
      (g.modulePullbackComplex ⋙ DerivedCategory.Q) ⋙ shiftFunctor _ n :=
  Functor.whiskerRight (DerivedCategory.Q.commShiftIso n).inv (functor g) ≫
    Functor.whiskerLeft (shiftFunctor _ n) (counit g) ≫
    (Functor.isoWhiskerRight
      (@Functor.mapCochainComplexShiftIso _ _ _ _ _ _
        g.modulePullback (modulePullback_additive g) n) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft g.modulePullbackComplex (DerivedCategory.Q.commShiftIso n)).hom

/-- The shifted-target counit is the shift of the augmentation counit. -/
def shiftTargetCounit (n : ℤ) :
    DerivedCategory.Q ⋙ (functor g ⋙ shiftFunctor _ n) ⟶
      (g.modulePullbackComplex ⋙ DerivedCategory.Q) ⋙ shiftFunctor _ n :=
  Functor.whiskerRight (counit g) (shiftFunctor _ n)

/-- Shifting the source preserves the right Kan extension of degreewise pullback. -/
theorem shiftSource_isRightKanExtension (n : ℤ) :
    (shiftFunctor _ n ⋙ functor g).IsRightKanExtension (shiftSourceCounit g n) := sorry

/-- Shifting the target preserves the right Kan extension of degreewise pullback. -/
theorem shiftTarget_isRightKanExtension (n : ℤ) :
    (functor g ⋙ shiftFunctor _ n).IsRightKanExtension (shiftTargetCounit g n) := sorry

/-- The shift comparison is the unique isomorphism of the two shifted right Kan extensions. -/
def shiftIso (n : ℤ) : shiftFunctor _ n ⋙ functor g ≅ functor g ⋙ shiftFunctor _ n :=
  @Functor.rightKanExtensionUnique _ _ _ _ _ _
    (shiftFunctor _ n ⋙ functor g) DerivedCategory.Q
    ((g.modulePullbackComplex ⋙ DerivedCategory.Q) ⋙ shiftFunctor _ n)
    (shiftSourceCounit g n) (shiftSource_isRightKanExtension g n)
    (functor g ⋙ shiftFunctor _ n) (shiftTargetCounit g n)
    (shiftTarget_isRightKanExtension g n)

/-- Derived pullback transports Ext classes in any integer degree by its canonical shift map. -/
def mapExt {K L : Hom.ModuleDerived.{w} (ofCommRingSheaf JY OY)}
    {n : ℤ} (ξ : Ext⁽n⁾(K, L)) : Ext⁽n⁾((functor g).obj K, (functor g).obj L) :=
  (functor g).map ξ ≫ (shiftIso g n).hom.app L

/-- Ext transport applies derived pullback and then its shift comparison. -/
theorem mapExt_apply {K L : Hom.ModuleDerived.{w} (ofCommRingSheaf JY OY)}
    {n : ℤ} (ξ : Ext⁽n⁾(K, L)) :
    mapExt g ξ = (functor g).map ξ ≫ (shiftIso g n).hom.app L := sorry

/-- Ext transport sends the zero class to zero. -/
theorem mapExt_zero {K L : Hom.ModuleDerived.{w} (ofCommRingSheaf JY OY)} (n : ℤ) :
    mapExt g (0 : Ext⁽n⁾(K, L)) = 0 := sorry

end RingedSite.ToposHom.DerivedPullback
