module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.GlobalSections
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

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Hom.ModuleDerived`, `Qh`, and `totalRightDerived` of module global sections must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): `mapHomotopyCategory` of `Hom.moduleGlobalSectionsAdditiveFunctor` in `rGammaDirectImageHomotopyIso` must use the named additive structure of that functor, not a freshly synthesized `Functor.Additive`.
attribute [local instance] Hom.moduleGlobalSectionsAdditiveFunctor_additive
-- Local instance justification (defeq pin): homotopy lifts of `Hom.moduleGlobalSectionsFunctor` must use the named additivity theorem that defines `Hom.moduleGlobalSectionsToDerived`, not a competing additive instance.
attribute [local instance] Hom.moduleGlobalSectionsFunctor_additive
-- Local instance justification (defeq pin): `totalRightDerivedUnit` of `Hom.moduleGlobalSectionsToDerived` must use the named `HasRightDerivedFunctor` instance that defines `Hom.moduleGlobalSectionsDerived`.
attribute [local instance] Hom.moduleGlobalSectionsToDerived_hasRightDerivedFunctor

/-- Restriction of scalars does not change the underlying abelian group. -/
def restrictScalarsCompForget₂Iso {R S : Type w} [Ring R] [Ring S] (f : R →+* S) :
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

/-- `directImageCompGlobalSectionsIso` is `moduleGlobalSectionsPushforwardIso` after
`forget₂`, transported along `Hom.moduleGlobalSectionsForget_eq`. -/
theorem directImageCompGlobalSectionsIso_eq :
    directImageCompGlobalSectionsIso K =
      isoWhiskerLeft (toAmbient K.simplicial).modulePushforward
          (eqToIso (Hom.moduleGlobalSectionsForget_eq.{w} X).symm) ≪≫
        isoWhiskerRight (toAmbient K.simplicial).moduleGlobalSectionsPushforwardIso
          (forget₂ (_root_.ModuleCat.{w} (Hom.globalSectionsRing X)) AddCommGrpCat.{w}) ≪≫
        isoWhiskerLeft (Hom.moduleGlobalSectionsFunctor.{w} (site K.simplicial))
          (restrictScalarsCompForget₂Iso
            (toAmbient K.simplicial).globalSectionsMap.hom) ≪≫
        eqToIso (Hom.moduleGlobalSectionsForget_eq.{w} (site K.simplicial)) :=
  sorry

/-- Homotopy-level identification of `a_* ⋙ Γ(C, -)` with `Γ((C / K)_total, -)`. -/
def rGammaDirectImageHomotopyIso :
    (toAmbient K.simplicial).modulePushforward.mapHomotopyCategory (up ℤ) ⋙
      Hom.moduleGlobalSectionsToDerived.{w} X ≅
    Hom.moduleGlobalSectionsToDerived.{w} (site K.simplicial) :=
  (associator
      ((toAmbient K.simplicial).modulePushforward.mapHomotopyCategory (up ℤ))
      ((Hom.moduleGlobalSectionsAdditiveFunctor.{w} X).mapHomotopyCategory (up ℤ))
      DerivedCategory.Qh).symm ≪≫
    isoWhiskerRight
      (mapHomotopyCategoryCompIso (directImageCompGlobalSectionsIso K) (up ℤ))
      DerivedCategory.Qh

/-- The iterated unit exhibiting `Ra_* ⋙ RΓ(C, -)` as a right-derived model of
`a_* ⋙ Γ(C, -)`. -/
def rGammaDirectImageUnit :
    (toAmbient K.simplicial).modulePushforward.mapHomotopyCategory (up ℤ) ⋙
      Hom.moduleGlobalSectionsToDerived.{w} X ⟶
    Hom.moduleLocalization.{w} (site K.simplicial) ⋙
      modulePushforwardDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} X :=
  whiskerLeft ((toAmbient K.simplicial).modulePushforward.mapHomotopyCategory (up ℤ))
      (totalRightDerivedUnit (Hom.moduleGlobalSectionsToDerived.{w} X)
        (Hom.moduleLocalization.{w} X) (Hom.ModuleQis.{w} X)) ≫
    (associator
        ((toAmbient K.simplicial).modulePushforward.mapHomotopyCategory (up ℤ))
        (Hom.moduleLocalization.{w} X)
        (Hom.moduleGlobalSectionsDerived.{w} X)).inv ≫
    whiskerRight
      (totalRightDerivedUnit
        (ToposHom.modulePushforwardToDerived (toAmbient K.simplicial))
        (Hom.moduleLocalization.{w} (site K.simplicial))
        (Hom.ModuleQis.{w} (site K.simplicial)))
      (Hom.moduleGlobalSectionsDerived.{w} X) ≫
    (associator (Hom.moduleLocalization.{w} (site K.simplicial))
        (modulePushforwardDerived K)
        (Hom.moduleGlobalSectionsDerived.{w} X)).hom

/-- The iterated model `Ra_* ⋙ RΓ(C, -)` is a right-derived functor of `a_* ⋙ Γ(C, -)`. -/
instance rGammaDirectImage_isRightDerived :
    (modulePushforwardDerived K ⋙
        Hom.moduleGlobalSectionsDerived.{w} X).IsRightDerivedFunctor
      (rGammaDirectImageUnit K) (Hom.ModuleQis.{w} (site K.simplicial)) :=
  sorry

/-- Leray identification `Ra_* ⋙ RΓ(C, -) ≅ RΓ((C / K)_total, -)` in `D(Ab)`. -/
def rGammaDirectImageIso :
    modulePushforwardDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} X ≅
    Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial) :=
  rightDerivedNatIso
    (modulePushforwardDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} X)
    (Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial))
    (rGammaDirectImageUnit K)
    (totalRightDerivedUnit (Hom.moduleGlobalSectionsToDerived.{w} (site K.simplicial))
      (Hom.moduleLocalization.{w} (site K.simplicial))
      (Hom.ModuleQis.{w} (site K.simplicial)))
    (Hom.ModuleQis.{w} (site K.simplicial))
    (rGammaDirectImageHomotopyIso K)

/-- `rGammaDirectImageIso` is `rightDerivedNatIso` of `rGammaDirectImageHomotopyIso`. -/
theorem rGammaDirectImageIso_eq :
    rGammaDirectImageIso K =
      rightDerivedNatIso
        (modulePushforwardDerived K ⋙ Hom.moduleGlobalSectionsDerived.{w} X)
        (Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial))
        (rGammaDirectImageUnit K)
        (totalRightDerivedUnit (Hom.moduleGlobalSectionsToDerived.{w} (site K.simplicial))
          (Hom.moduleLocalization.{w} (site K.simplicial))
          (Hom.ModuleQis.{w} (site K.simplicial)))
        (Hom.ModuleQis.{w} (site K.simplicial))
        (rGammaDirectImageHomotopyIso K) :=
  sorry

/-- Canonical comparison `RΓ(C, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)`. -/
def rGammaPullbackComparison :
    Hom.moduleGlobalSectionsDerived.{w} X ⟶
      modulePullbackDerived K ⋙
        Hom.moduleGlobalSectionsDerived.{w} (site K.simplicial) :=
  whiskerRight (derivedUnit K) (Hom.moduleGlobalSectionsDerived.{w} X) ≫
    (associator (modulePullbackDerived K) (modulePushforwardDerived K)
        (Hom.moduleGlobalSectionsDerived.{w} X)).hom ≫
    whiskerLeft (modulePullbackDerived K) (rGammaDirectImageIso K).hom

/-- `rGammaPullbackComparison` is the derived unit of `La^* ⊣ Ra_*`, reassociated and
postcomposed with the Leray identification `rGammaDirectImageIso`. -/
theorem rGammaPullbackComparison_eq :
    rGammaPullbackComparison K =
      whiskerRight (derivedUnit K) (Hom.moduleGlobalSectionsDerived.{w} X) ≫
        (associator (modulePullbackDerived K) (modulePushforwardDerived K)
            (Hom.moduleGlobalSectionsDerived.{w} X)).hom ≫
        whiskerLeft (modulePullbackDerived K) (rGammaDirectImageIso K).hom :=
  sorry

/-- The component of `rGammaPullbackComparison` at `E` is
`RΓ(C, E) ⟶ RΓ((C / K)_total, La^* E)`. -/
theorem rGammaPullbackComparison_app (E : Hom.ModuleDerived.{w} X) :
    (rGammaPullbackComparison K).app E =
      (Hom.moduleGlobalSectionsDerived.{w} X).map ((derivedUnit K).app E) ≫
        (rGammaDirectImageIso K).hom.app ((modulePullbackDerived K).obj E) :=
  sorry

end RingedSite.Localization.AtSimplicialSR
