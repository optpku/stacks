module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import stacks_project.Chap61.Theorem_61_30_1_Reduction
public import stacks_project.Chap61.Theorem_61_30_1_BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Theorem 61.30.1

Proper base change for derived-complete complexes on small pro-étale sites.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open ComplexShape
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
open AlgebraicGeometry.Scheme.ProetaleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
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
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient f Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient g Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient f' Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient g' Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(Functor.Homotopy.toDerived
    (RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
      (ofConstantCoefficient g Λ)).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(Functor.Homotopy.toDerived
    (RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
      (ofConstantCoefficient f Λ)).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [CategoryTheory.Adjunction.TotalDerived.HasPair
    (G := (ofConstantCoefficient f Λ).modulePullback.mapHomotopyCategory (ComplexShape.up ℤ))
    (F := (ofConstantCoefficient f Λ).modulePushforward.mapHomotopyCategory (ComplexShape.up ℤ))
    (RingedSite.Hom.ModuleQis
      (RingedSite.ofCommRingSheaf (ProEt.topology Y) (constantCoefficientRing Y Λ)))
    (RingedSite.Hom.ModuleQis
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)))
    (L1 := RingedSite.Hom.moduleLocalization
      (RingedSite.ofCommRingSheaf (ProEt.topology Y) (constantCoefficientRing Y Λ)))
    (L2 := RingedSite.Hom.moduleLocalization
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)))]
variable [CategoryTheory.Adjunction.TotalDerived.HasPair
    (G := (ofConstantCoefficient f' Λ).modulePullback.mapHomotopyCategory (ComplexShape.up ℤ))
    (F := (ofConstantCoefficient f' Λ).modulePushforward.mapHomotopyCategory (ComplexShape.up ℤ))
    (RingedSite.Hom.ModuleQis
      (RingedSite.ofCommRingSheaf (ProEt.topology Y') (constantCoefficientRing Y' Λ)))
    (RingedSite.Hom.ModuleQis
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (L1 := RingedSite.Hom.moduleLocalization
      (RingedSite.ofCommRingSheaf (ProEt.topology Y') (constantCoefficientRing Y' Λ)))
    (L2 := RingedSite.Hom.moduleLocalization
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))]
variable [CategoryTheory.Adjunction.TotalDerived.HasPair
    (G := (ofConstantCoefficient g Λ).modulePullback.mapHomotopyCategory (ComplexShape.up ℤ))
    (F := (ofConstantCoefficient g Λ).modulePushforward.mapHomotopyCategory (ComplexShape.up ℤ))
    (RingedSite.Hom.ModuleQis
      (RingedSite.ofCommRingSheaf (ProEt.topology Y) (constantCoefficientRing Y Λ)))
    (RingedSite.Hom.ModuleQis
      (RingedSite.ofCommRingSheaf (ProEt.topology Y') (constantCoefficientRing Y' Λ)))
    (L1 := RingedSite.Hom.moduleLocalization
      (RingedSite.ofCommRingSheaf (ProEt.topology Y) (constantCoefficientRing Y Λ)))
    (L2 := RingedSite.Hom.moduleLocalization
      (RingedSite.ofCommRingSheaf (ProEt.topology Y') (constantCoefficientRing Y' Λ)))]

/-- Theorem 61.30.1: for a proper morphism of schemes, a cartesian base-change
square, a Noetherian coefficient ring Λ with ideal I such that Λ ⧸ I is torsion,
and a derived-complete object K of D(X_proétale, Λ) whose reductions
K ⊗^L underline(Λ ⧸ I^n) are bounded below with cohomology sheaves coming from
X_étale, and with each Λ ⧸ I^n a perfect Λ-module, the completed derived
base-change map Lg_comp^* Rf_* K ⟶ Rf'_* L(g')_comp^* K is an isomorphism. -/
@[stacks 09C9]
theorem completedDerivedBaseChange_isIso_of_isProper
    [IsProper f] (h_cart : IsPullback g' f' f g) (I : Ideal Λ)
    (h_torsion : AddMonoid.IsTorsion (Λ ⧸ I))
    (h_perf : ∀ n, ModuleCat.IsPerfect (ModuleCat.of Λ (Λ ⧸ I ^ n)))
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
    (h_bdd : ∀ (n : ℕ)
      [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
      [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
      [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
      [(Functor.Homotopy.toDerived
          (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))],
      IsProEtReductionBoundedBelow I n (toDerivedCategory K))
    (h_etale : ∀ (n : ℕ)
      [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
      [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
      [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
      [(Functor.Homotopy.toDerived
          (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
      [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
      [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ n),
        (etaleToProEt X).op.HasLeftKanExtension F],
      IsProEtReductionCohomologyFromEtale I n (toDerivedCategory K)) :
    IsIso
      (completedDerivedBaseChangeHom f Λ g f' g' h_cart I
        (toConstantComplete Λ I K hK)) := sorry

end AlgebraicGeometry.Scheme.ProEt

end

end
