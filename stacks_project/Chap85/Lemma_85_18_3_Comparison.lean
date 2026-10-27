/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedGlobalSections
public import stacks_project.Chap85.Lemma_85_18_2_Adjunction

/-!
# Derived global-sections comparison for a hypercovering of modules

If `K` is a hypercovering of the terminal presheaf, derived global sections of
`O_C`-modules identify after `Ra_*` with derived global sections on
`(C / K)_total`. The canonical comparison
`RΓ(C, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)` is the derived unit of `La^* ⊣ Ra_*`
followed by that Leray identification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (overSiteDiagram overSiteTotalTopology totalForget)

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
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient K.simplicial).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived (toAmbient K.simplicial)]
variable [ToposHom.HasModulePushforwardDerived (toAmbient K.simplicial)]
variable [HasModuleDerivedAdjunction K]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify (site K.simplicial).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (site K.simplicial).siteTopology AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (site K.simplicial))]

/- The underived direct-image/global-sections identification after forgetting scalars. -/
#check (RingedSite.Localization.AtSimplicialSR.directImageCompGlobalSectionsIso K :
  (toAmbient K.simplicial).modulePushforward ⋙ Hom.moduleGlobalSectionsAdditiveFunctor.{w} X ≅
    Hom.moduleGlobalSectionsAdditiveFunctor.{w} (site K.simplicial))

/- The canonical homotopy-level global-sections identification. -/
#check (RingedSite.Localization.AtSimplicialSR.rGammaDirectImageHomotopyIso K :
  modulePushforwardHomotopy K.simplicial ⋙ Hom.moduleGlobalSectionsToDerived.{w} X ≅
    Hom.moduleGlobalSectionsToDerived.{w} (site K.simplicial))

/- The iterated unit for derived direct image followed by global sections. -/
#check (RingedSite.Localization.AtSimplicialSR.rGammaDirectImageUnit K :
  modulePushforwardHomotopy K.simplicial ⋙ Hom.moduleGlobalSectionsToDerived.{w} X ⟶
    Hom.moduleLocalization.{w} (site K.simplicial) ⋙
      modulePushforwardDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} X)

/- The iterated model is a right-derived functor. -/
#check (RingedSite.Localization.AtSimplicialSR.rGammaDirectImage_isRightDerived K :
  (modulePushforwardDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} X).IsRightDerivedFunctor
    (rGammaDirectImageUnit K) (Hom.ModuleQis.{w} (site K.simplicial)))

/- The canonical Leray identification in the unbounded derived category. -/
#check (RingedSite.Localization.AtSimplicialSR.rGammaDirectImageIso K :
  modulePushforwardDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} X ≅
    Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial))

/- The global-sections comparison is induced by the canonical derived adjunction unit. -/
#check (RingedSite.Localization.AtSimplicialSR.rGammaPullbackComparison K :
  Hom.moduleGlobalSectionsDerived.{w} X ⟶
    modulePullbackDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial))

/- The component formula for the canonical global-sections comparison. -/
#check (RingedSite.Localization.AtSimplicialSR.rGammaPullbackComparison_app K :
  ∀ E : Hom.ModuleDerived.{w} X,
    (rGammaPullbackComparison K).app E =
      (Hom.moduleGlobalSectionsDerived.{w} X).map ((derivedUnit K).app E) ≫
        (rGammaDirectImageIso K).hom.app ((modulePullbackDerived K).obj E))

end RingedSite.Localization.AtSimplicialSR
