/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback.KFlat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import ReasLib.CategoryTheory.Functor.Derived.Deformation

/-! # Derived inverse image from functorial cell complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom.NativeDerived.CellPullback

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
  [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasSheafify JX AddCommGrpCat.{w}] [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JY AddCommGrpCat.{w}] [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable (f : ToposHom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY))
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- Standard localization of complexes of module sheaves with native addition of morphisms. -/
abbrev Q (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{w})
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :=
  @DerivedCategory.Q (ModuleCat.{w} (ofCommRingSheaf J O)) _
    (RingedSite.NativeDerived.abelian.{w} (ofCommRingSheaf J O))
    (RingedSite.NativeDerived.hasDerivedCategory.{w} (ofCommRingSheaf J O))

/-- Degreewise pullback of the actual functorial cell replacement. -/
def cochain :=
  SheafOfModules.CellReplacement.functor ⋙ f.modulePullbackComplex

/-- Localized pullback of cell replacements inverts quasi-isomorphisms. -/
theorem invertsQuasiIso :
    (HomologicalComplex.quasiIso (ModuleCat.{w} (ofCommRingSheaf JY OY)) (up ℤ)).IsInvertedBy
      (cochain f ⋙ Q JX OX) := sorry

/-- Derived inverse image constructed by localizing actual pulled-back cell replacements. -/
def functor : RingedSite.NativeDerived.category.{w} (ofCommRingSheaf JY OY) ⥤
    RingedSite.NativeDerived.category.{w} (ofCommRingSheaf JX OX) :=
  Localization.lift (cochain f ⋙ Q JX OX) (invertsQuasiIso f) (Q JY OY)

/-- Derived inverse image on a complex is its localized pulled-back cell replacement. -/
def computation : Q JY OY ⋙ functor f ≅ cochain f ⋙ Q JX OX :=
  Localization.fac (cochain f ⋙ Q JX OX) (invertsQuasiIso f) (Q JY OY)

/-- Pullback of the augmentation of a K-flat cell model is a quasi-isomorphism. -/
theorem augmentationOnModels_quasiIso
    (K : CochainComplex (ModuleCat.{w} (ofCommRingSheaf JY OY)) ℤ) :
    QuasiIso (f.modulePullbackComplex.map
      (SheafOfModules.CellReplacement.augmentation
        (SheafOfModules.CellReplacement.model K))) := sorry

/-- The derived inverse-image counit comes from the original cell augmentation. -/
def counit : Q JY OY ⋙ functor f ⟶ f.modulePullbackComplex ⋙ Q JX OX :=
  Functor.LeftDerived.Deformation.counit (Q JY OY)
    SheafOfModules.CellReplacement.functor SheafOfModules.CellReplacement.augmentationNatTrans
    (f.modulePullbackComplex ⋙ Q JX OX) (functor f) (computation f)

/-- The cell inverse-image model carries the explicit augmentation-based universal extension maps. -/
def derivedModel : Functor.LeftDerived.Model (f.modulePullbackComplex ⋙ Q JX OX)
    (Q JY OY) (HomologicalComplex.quasiIso (ModuleCat.{w} (ofCommRingSheaf JY OY)) (up ℤ)) :=
  ⟨functor f, counit f,
    Functor.LeftDerived.Deformation.isLeftDerived (Q JY OY)
      (HomologicalComplex.quasiIso (ModuleCat.{w} (ofCommRingSheaf JY OY)) (up ℤ))
      SheafOfModules.CellReplacement.functor SheafOfModules.CellReplacement.augmentationNatTrans
      (fun K ↦ SheafOfModules.CellReplacement.augmentation_quasiIso K)
      (f.modulePullbackComplex ⋙ Q JX OX) (functor f) (computation f)
      (fun K ↦ Localization.inverts (Q JX OX)
        (HomologicalComplex.quasiIso (ModuleCat.{w} (ofCommRingSheaf JX OX)) (up ℤ)) _
        (augmentationOnModels_quasiIso f K))⟩

end RingedSite.ToposHom.NativeDerived.CellPullback
