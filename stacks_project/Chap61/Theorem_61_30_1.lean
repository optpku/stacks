/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.ProperBaseChange
import StacksCheckRecall

/-! Proper base change for derived-complete complexes on small pro-étale sites. -/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open ComplexShape
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
open AlgebraicGeometry.Scheme.ProetaleDerived
open RingedSite.Hom.ModuleDerived
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable {Λ : Type (u + 1)} [CommRing Λ]
variable [UnivLE.{u + 1, u + 1}]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) CommRingCat.{u + 1}]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) RingCat.{u + 1}]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) (Type (u + 1))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1}]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).HasSheafCompose (CategoryTheory.forget RingCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).HasSheafCompose (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).PreservesSheafification (CategoryTheory.forget RingCat.{u + 1})]
variable [∀ Z : Scheme.{u}, (ProEt.topology Z).WEqualsLocallyBijective RingCat.{u + 1}]
variable [∀ Z : Scheme.{u}, (ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [∀ Z : Scheme.{u}, HasGlobalSectionsFunctor (ProEt.topology Z) (Type (u + 1))]
variable [∀ Z : Scheme.{u},
    LocallySmall (SheafOfModules (Sheaf.ringSheafOfComm
      (constantCoefficientRing Z Λ)))]
variable [∀ Z : Scheme.{u},
    WellPowered (SheafOfModules (Sheaf.ringSheafOfComm
      (constantCoefficientRing Z Λ)))]
variable [∀ Z : Scheme.{u}, ∀ U : Z.ProEt,
    HasWeakSheafify ((ProEt.topology Z).over U) AddCommGrpCat.{u + 1}]
variable [∀ Z : Scheme.{u}, ∀ U : Z.ProEt,
    ((ProEt.topology Z).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (ProEt.topology X') (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (ProEt.topology Y') (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [Abelian (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} Λ))]
variable [Abelian (Sheaf (ProEt.topology Y') (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology Y') (ModuleCat.{u + 1} Λ))]
variable [CategoryWithHomology (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange f).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange f).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology X))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange g).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange g).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology Y'))]
variable [∀ P : Y'.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange f').op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange f').sheafPullback (Type (u + 1)) (ProEt.topology Y') (ProEt.topology X'))]
variable [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange g').op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange g').sheafPullback (Type (u + 1)) (ProEt.topology X) (ProEt.topology X'))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange (g' ≫ f)).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange (g' ≫ f)).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology X'))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange (f' ≫ g)).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange (f' ≫ g)).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology X'))]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient f Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient g Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient f' Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient g' Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
      (ofConstantCoefficient f Λ)).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
      (ofConstantCoefficient g Λ)).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient (g' ≫ f) Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient (f' ≫ g) Λ).structureMap).IsRightAdjoint]
variable [(ofConstantCoefficient f Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient f Λ).HasModulePushforwardDerived]
variable [(ofConstantCoefficient g Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient g Λ).HasModulePushforwardDerived]
variable [(ofConstantCoefficient f' Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient f' Λ).HasModulePushforwardDerived]
variable [(ofConstantCoefficient g' Λ).HasModulePullbackDerived]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
    (ofConstantCoefficient g Λ)).HasModulePullbackDerived]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
    (ofConstantCoefficient f Λ)).HasModulePullbackDerived]
variable [(ofConstantCoefficient f Λ).modulePullback.Additive]
variable [(ofConstantCoefficient g Λ).modulePullback.Additive]
variable [(ofConstantCoefficient f' Λ).modulePullback.Additive]
variable [(ofConstantCoefficient g' Λ).modulePullback.Additive]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
    (ofConstantCoefficient g Λ)).modulePullback.Additive]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
    (ofConstantCoefficient f Λ)).modulePullback.Additive]
variable [(baseChange f ⋙ baseChange g').IsContinuous
    (ProEt.topology Y) (ProEt.topology X')]
variable [(baseChange g ⋙ baseChange f').IsContinuous
    (ProEt.topology Y) (ProEt.topology X')]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)))
    (ofConstantCoefficient f Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology Y') (constantCoefficientRing Y' Λ)))
    (ofConstantCoefficient g Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (ofConstantCoefficient f' Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (ofConstantCoefficient g' Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
      (ofConstantCoefficient g Λ)).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
      (ofConstantCoefficient f Λ)).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (ofConstantCoefficient f Λ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (ofConstantCoefficient f' Λ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (ofConstantCoefficient g Λ)]

/- Theorem 61.30.1: Proper base change for derived-complete complexes on small pro-étale sites. -/
@[stacks 09C9] #check
  (AlgebraicGeometry.Scheme.ProEt.completedDerivedBaseChange_isIso_of_isProper_withReflectors f g f' g' :
  ∀ [IsNoetherianRing Λ] [IsProper f] (h_cart : IsPullback g' f' f g) (I : Ideal Λ)
    (RX : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal X' Λ I)))
    (RY : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal Y' Λ I)))
    (_ : AddMonoid.IsTorsion (Λ ⧸ I))
    (_ : ∀ n, ModuleCat.IsPerfect (ModuleCat.of Λ (Λ ⧸ I ^ n)))
    (K : ProetaleDerived X Λ)
    (hK : IsDerivedCompleteWithRespectTo K I)
    [(coefficientIdeal X Λ I :
        SheafOfModules.RingedSite.ringedSiteModuleCategory
          (ProEt.topology X) (constantCoefficientRing X Λ)).IsFiniteType]
    [(coefficientIdeal X' Λ I :
        SheafOfModules.RingedSite.ringedSiteModuleCategory
          (ProEt.topology X') (constantCoefficientRing X' Λ)).IsFiniteType]
    [(coefficientIdeal Y' Λ I :
        SheafOfModules.RingedSite.ringedSiteModuleCategory
          (ProEt.topology Y') (constantCoefficientRing Y' Λ)).IsFiniteType]
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    [∀ n : ℕ, HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [∀ n : ℕ,
      HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [∀ n : ℕ, (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [∀ n : ℕ, (Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [∀ n : ℕ, HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [∀ n : ℕ,
      HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [∀ (n : ℕ) (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ n)),
      (etaleToProEt X).op.HasLeftKanExtension F]
    (_ : ∀ n : ℕ, IsBoundedBelow (proEtReduction I n K))
    (_ : ∀ n : ℕ,
      cohomologyIn (etaleToProEtModuleEssImage X (Λ ⧸ I ^ n)) (proEtReduction I n K)),
    IsIso
      (AlgebraicGeometry.Scheme.ProEt.completedDerivedBaseChangeHomWithReflectors f g f' g' h_cart I RX RY
        (toConstantComplete Λ I K hK)))

end AlgebraicGeometry.Scheme.ProEt

end

end
