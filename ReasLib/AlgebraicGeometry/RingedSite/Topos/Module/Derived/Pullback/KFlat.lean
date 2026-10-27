/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.Algebra.Homology.DerivedCategory.Monoidal.KFlat.TermwiseFlat

/-! # Native derived pullback on K-flat complexes with flat terms -/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom.NativeDerived

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
  [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}] [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}] [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [Abelian (ModuleCat.{w} (ofCommRingSheaf JX OX))]
  [Abelian (ModuleCat.{w} (ofCommRingSheaf JY OY))]
variable (f : ToposHom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY))
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- Degreewise pullback preserves K-flat homotopy objects represented by complexes with flat terms. -/
theorem goodModelPullback_mem
    (K : Hom.ModuleHomotopy.{w} (ofCommRingSheaf JY OY))
    (hK : HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (ofCommRingSheaf JY OY)) K) :
    HomotopyCategory.KFlat.termwiseFlat (ModuleCat.{w} (ofCommRingSheaf JX OX))
      (f.modulePullbackHomotopy.obj K) := sorry

/-- Pullback restricted to K-flat homotopy objects with flat terms. -/
def goodModelPullback :
    HomotopyCategory.KFlat.TermwiseFlat (ModuleCat.{w} (ofCommRingSheaf JY OY)) ⥤
      HomotopyCategory.KFlat.TermwiseFlat (ModuleCat.{w} (ofCommRingSheaf JX OX)) :=
  (HomotopyCategory.KFlat.termwiseFlat _).lift
    ((HomotopyCategory.KFlat.termwiseFlat _).ι ⋙ f.modulePullbackHomotopy)
    (fun K ↦ goodModelPullback_mem f K.obj K.property)

/-- Restricted pullback followed by inclusion agrees with pullback of the included complex. -/
def goodModelPullbackCompInclusionIso :
    goodModelPullback f ⋙ (HomotopyCategory.KFlat.termwiseFlat _).ι ≅
      (HomotopyCategory.KFlat.termwiseFlat _).ι ⋙ f.modulePullbackHomotopy :=
  Iso.refl _

/-- The canonical derived counit on K-flat homotopy objects with flat terms, expressed through
localization of those good models. -/
def goodModelComparison [HasPullback f] :
    @DerivedCategory.KFlat.TermwiseFlat.localizationFunctor _ _
        (RingedSite.NativeDerived.abelian.{w} (ofCommRingSheaf JY OY))
        (RingedSite.NativeDerived.hasDerivedCategory.{w} (ofCommRingSheaf JY OY)) _ _ ⋙
      pullback f ⟶
    goodModelPullback f ⋙
      @DerivedCategory.KFlat.TermwiseFlat.localizationFunctor _ _
        (RingedSite.NativeDerived.abelian.{w} (ofCommRingSheaf JX OX))
        (RingedSite.NativeDerived.hasDerivedCategory.{w} (ofCommRingSheaf JX OX)) _ _ :=
  Functor.whiskerRight
      (@DerivedCategory.KFlat.TermwiseFlat.localizationFunctorIso _ _
        (RingedSite.NativeDerived.abelian.{w} (ofCommRingSheaf JY OY))
        (RingedSite.NativeDerived.hasDerivedCategory.{w} (ofCommRingSheaf JY OY)) _ _).hom
      (pullback f) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.KFlat.termwiseFlat _).ι
      (@Functor.totalLeftDerivedCounit _ _ _ _ _ _ (pullbackToDerived f)
        (RingedSite.NativeDerived.localization.{w} (ofCommRingSheaf JY OY))
        (RingedSite.NativeDerived.quasiIso.{w} (ofCommRingSheaf JY OY))
        (RingedSite.NativeDerived.localizationIsLocalization.{w} (ofCommRingSheaf JY OY))
        inferInstance) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (goodModelPullbackCompInclusionIso f).inv _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (goodModelPullback f)
      (@DerivedCategory.KFlat.TermwiseFlat.localizationFunctorIso _ _
        (RingedSite.NativeDerived.abelian.{w} (ofCommRingSheaf JX OX))
        (RingedSite.NativeDerived.hasDerivedCategory.{w} (ofCommRingSheaf JX OX)) _ _).inv

end RingedSite.ToposHom.NativeDerived
