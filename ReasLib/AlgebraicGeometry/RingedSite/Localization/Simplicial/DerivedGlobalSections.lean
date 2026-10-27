/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedModuleDescent

/-!
# Derived global-sections comparison for a hypercovering of modules

If `K` is a hypercovering of the terminal presheaf, derived global sections of
`O_C`-modules identify after `Ra_*` with derived global sections on
`(C / K)_total`. The canonical comparison
`RΓ(C, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)` is the derived unit of `La^* ⊣ Ra_*`
followed by that Leray identification.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (overSiteDiagram overSiteTotalTopology totalForget)

/-- Restriction of scalars does not change the underlying abelian group. -/
private def restrictScalarsCompForget₂Iso {R S : Type w} [Ring R] [Ring S] (f : R →+* S) :
    _root_.ModuleCat.restrictScalars.{w} f ⋙
      forget₂ (_root_.ModuleCat.{w} R) AddCommGrpCat.{w} ≅
    forget₂ (_root_.ModuleCat.{w} S) AddCommGrpCat.{w} :=
  Iso.refl _

variable {X : RingedSite.{u, v, w}}
variable [h_eq : HasEqualizers X.carrier] [h_pb : HasPullbacks X.carrier]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [UnivLE.{u, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify (site K.simplicial).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (site K.simplicial).siteTopology AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (site K.simplicial))]

/-- Underived identification `Γ((C / K)_total, -) ≅ Γ(C, a_* -)` after forgetting to `Ab`. -/
def directImageCompGlobalSectionsIso :
    (toAmbient K.simplicial).modulePushforward ⋙
      Hom.moduleGlobalSectionsAdditiveFunctor.{w} X ≅
    Hom.moduleGlobalSectionsAdditiveFunctor.{w} (site K.simplicial) :=
  isoWhiskerLeft (toAmbient K.simplicial).modulePushforward
      (eqToIso (Hom.moduleGlobalSectionsForget_eq.{w} X).symm) ≪≫
    isoWhiskerRight (toAmbient K.simplicial).moduleGlobalSectionsPushforwardIso
      (forget₂ (_root_.ModuleCat.{w} (Hom.globalSectionsRing X)) AddCommGrpCat.{w}) ≪≫
    isoWhiskerLeft (Hom.moduleGlobalSectionsFunctor.{w} (site K.simplicial))
      (restrictScalarsCompForget₂Iso (toAmbient K.simplicial).globalSectionsMap.hom) ≪≫
    eqToIso (Hom.moduleGlobalSectionsForget_eq.{w} (site K.simplicial))

/-- Homotopy-level identification of `a_* ⋙ Γ(C, -)` with `Γ((C / K)_total, -)`. -/
def rGammaDirectImageHomotopyIso :
    modulePushforwardHomotopy K.simplicial ⋙
      Hom.moduleGlobalSectionsToDerived.{w} X ≅
    Hom.moduleGlobalSectionsToDerived.{w} (site K.simplicial) :=
  (associator (modulePushforwardHomotopy K.simplicial)
      (@Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (Hom.moduleGlobalSectionsAdditiveFunctor.{w} X)
        (Hom.moduleGlobalSectionsAdditiveFunctor_additive X) (up ℤ))
      DerivedCategory.Qh).symm ≪≫
    isoWhiskerRight
      (@mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
        (directImageCompGlobalSectionsIso K)
        (ToposHom.modulePushforward_additive (toAmbient K.simplicial))
        (Hom.moduleGlobalSectionsAdditiveFunctor_additive X)
        (Hom.moduleGlobalSectionsAdditiveFunctor_additive (site K.simplicial)) (up ℤ))
      DerivedCategory.Qh

/-- The iterated unit exhibiting `Ra_* ⋙ RΓ(C, -)` as a right-derived model of
`a_* ⋙ Γ(C, -)`. -/
def rGammaDirectImageUnit :
    modulePushforwardHomotopy K.simplicial ⋙
      Hom.moduleGlobalSectionsToDerived.{w} X ⟶
    Hom.moduleLocalization.{w} (site K.simplicial) ⋙
      derivedPushforward K.simplicial ⋙ Hom.moduleGlobalSectionsDerived.{w} X :=
  whiskerLeft (modulePushforwardHomotopy K.simplicial)
      (@totalRightDerivedUnit _ _ _ _ _ _ (Hom.moduleGlobalSectionsToDerived.{w} X)
        (Hom.moduleLocalization.{w} X) (Hom.ModuleQis.{w} X) inferInstance
        (Hom.moduleGlobalSectionsToDerived_hasRightDerivedFunctor X)) ≫
    (associator (modulePushforwardHomotopy K.simplicial) (Hom.moduleLocalization.{w} X)
        (Hom.moduleGlobalSectionsDerived.{w} X)).inv ≫
    whiskerRight
      (@totalRightDerivedUnit _ _ _ _ _ _
        (ToposHom.modulePushforwardToDerived (toAmbient K.simplicial))
        (Hom.moduleLocalization.{w} (site K.simplicial))
        (Hom.ModuleQis.{w} (site K.simplicial)) inferInstance
        (toAmbient_hasModulePushforwardDerived K.simplicial))
      (Hom.moduleGlobalSectionsDerived.{w} X) ≫
    (associator (Hom.moduleLocalization.{w} (site K.simplicial)) (derivedPushforward K.simplicial)
        (Hom.moduleGlobalSectionsDerived.{w} X)).hom

/-- The iterated model `Ra_* ⋙ RΓ(C, -)` is a right-derived functor of `a_* ⋙ Γ(C, -)`. -/
@[instance] theorem rGammaDirectImage_isRightDerived :
    (derivedPushforward K.simplicial ⋙
        Hom.moduleGlobalSectionsDerived.{w} X).IsRightDerivedFunctor
      (rGammaDirectImageUnit K) (Hom.ModuleQis.{w} (site K.simplicial)) := sorry

/-- Leray identification `Ra_* ⋙ RΓ(C, -) ≅ RΓ((C / K)_total, -)` in `D(Ab)`. -/
def rGammaDirectImageIso :
    derivedPushforward K.simplicial ⋙ Hom.moduleGlobalSectionsDerived.{w} X ≅
    Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial) :=
  @rightDerivedNatIso _ _ _ _ _ _
    (derivedPushforward K.simplicial ⋙ Hom.moduleGlobalSectionsDerived.{w} X)
    (Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial))
    _ _ _ (rGammaDirectImageUnit K)
    (@totalRightDerivedUnit _ _ _ _ _ _ (Hom.moduleGlobalSectionsToDerived.{w} (site K.simplicial))
      (Hom.moduleLocalization.{w} (site K.simplicial))
      (Hom.ModuleQis.{w} (site K.simplicial)) inferInstance
      (Hom.moduleGlobalSectionsToDerived_hasRightDerivedFunctor (site K.simplicial)))
    (Hom.ModuleQis.{w} (site K.simplicial))
    inferInstance (rGammaDirectImage_isRightDerived K) inferInstance
    (rGammaDirectImageHomotopyIso K)

/-- Canonical comparison `RΓ(C, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)`. -/
def rGammaPullbackComparison :
    Hom.moduleGlobalSectionsDerived.{w} X ⟶
      derivedPullback K.simplicial ⋙
        Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial) :=
  whiskerRight (derivedUnit K) (Hom.moduleGlobalSectionsDerived.{w} X) ≫
    (associator (derivedPullback K.simplicial) (derivedPushforward K.simplicial)
        (Hom.moduleGlobalSectionsDerived.{w} X)).hom ≫
    whiskerLeft (derivedPullback K.simplicial) (rGammaDirectImageIso K).hom

/-- The component of `rGammaPullbackComparison` at `E` is
`RΓ(C, E) ⟶ RΓ((C / K)_total, La^* E)`. -/
theorem rGammaPullbackComparison_app (E : Hom.ModuleDerived.{w} X) :
    (rGammaPullbackComparison K).app E =
      (Hom.moduleGlobalSectionsDerived.{w} X).map ((derivedUnit K).app E) ≫
        (rGammaDirectImageIso K).hom.app ((derivedPullback K.simplicial).obj E) := sorry

/-- The canonical comparison of derived global sections with those of the derived
pullback to a terminal hypercovering is invertible at every unbounded derived module. -/
@[instance] theorem rGammaPullbackComparison_app_isIso (E : Hom.ModuleDerived.{w} X) :
    IsIso ((rGammaPullbackComparison K).app E) := sorry

/-- The canonical derived global-sections comparison for a terminal hypercovering
is an isomorphism of functors. -/
@[instance] theorem rGammaPullbackComparison_isIso :
    IsIso (rGammaPullbackComparison K) := sorry

end RingedSite.Localization.AtSimplicialSR
