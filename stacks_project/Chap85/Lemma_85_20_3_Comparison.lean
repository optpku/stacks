module

public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import stacks_project.Chap85.Lemma_85_18_3_Comparison
public import stacks_project.Chap85.Lemma_85_20_2_Adjunction

/-!
# Derived global-sections comparison for a hypercovering of an object, modules

If `K` is a hypercovering of an object `U`, Lemma 85.18.3 applied to the slice
ringed site `X.localization U` and `toSliceTerminal` supplies a Leray
identification `Ra_* ⋙ RΓ(X, -) ≅ RΓ((C / K)_total, -)` and the canonical
comparison `RΓ(X, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)

section Terminal

open Localization.AtSimplicialSR

variable (Y : RingedSite.{u, v, w})
variable [h_eq : HasEqualizers Y.carrier] [h_pbY : HasPullbacks Y.carrier]
include h_eq h_pbY
variable (L : HypercoveringOf.Terminal.{ι} Y.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [UnivLE.{u, w}]
variable [HasSheafify (overSiteTotalTopology Y.siteTopology L.simplicial) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram L.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget L.simplicial).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology Y.siteTopology L.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient L.simplicial).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived (toAmbient L.simplicial)]
variable [ToposHom.HasModulePushforwardDerived (toAmbient L.simplicial)]
variable [HasModuleDerivedAdjunction_terminal Y L]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify (site L.simplicial).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (site L.simplicial).siteTopology AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} Y)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (site L.simplicial))]

/-- Leray identification `Ra_* ⋙ RΓ(Y, -) ≅ RΓ((C / L)_total, -)` for a
site-level hypercovering, with the ambient ringed site explicit. -/
abbrev rGammaDirectImageIso_terminal :=
  rGammaDirectImageIso L

/-- `rGammaDirectImageIso_terminal` is the terminal-hypercovering Leray
identification. -/
theorem rGammaDirectImageIso_terminal_eq :
    rGammaDirectImageIso_terminal Y L = rGammaDirectImageIso L :=
  sorry

/-- Canonical comparison `RΓ(Y, -) ⟶ La^* ⋙ RΓ((C / L)_total, -)` for a
site-level hypercovering, with the ambient ringed site explicit. -/
abbrev rGammaPullbackComparison_terminal :=
  rGammaPullbackComparison L

/-- `rGammaPullbackComparison_terminal` is the terminal-hypercovering comparison. -/
theorem rGammaPullbackComparison_terminal_eq :
    rGammaPullbackComparison_terminal Y L = rGammaPullbackComparison L :=
  sorry

end Terminal

variable {X : RingedSite.{u, v, w}}
variable [h_pb : HasPullbacks X.carrier]
include h_pb
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology (X.localization U).siteTopology
    K.toSimplicialObject).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(X.localization U).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived
    (toAmbient_terminal (X.localization U) (toSliceTerminal X.siteTopology U K))]
variable [ToposHom.HasModulePushforwardDerived
    (toAmbient_terminal (X.localization U) (toSliceTerminal X.siteTopology U K))]
variable [HasModuleDerivedAdjunction U K]
variable [HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify
    (site_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor
    (site_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).siteTopology AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (X.localization U))]
variable [IsGrothendieckAbelian
    (RingedSite.ModuleCat.{w}
      (site_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)))]

/-- Leray identification `Ra_* ⋙ RΓ(X, -) ≅ RΓ((C / K)_total, -)` for a
hypercovering of an object. -/
abbrev rGammaDirectImageIso :=
  rGammaDirectImageIso_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- `rGammaDirectImageIso` is the slice instantiation of
`rGammaDirectImageIso_terminal`. -/
theorem rGammaDirectImageIso_eq :
    rGammaDirectImageIso U K =
      rGammaDirectImageIso_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- Canonical comparison `RΓ(X, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)` for a
hypercovering of an object. -/
abbrev rGammaPullbackComparison :=
  rGammaPullbackComparison_terminal (X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- `rGammaPullbackComparison` is the derived unit of `La^* ⊣ Ra_*`, reassociated
and postcomposed with the Leray identification `rGammaDirectImageIso`. -/
theorem rGammaPullbackComparison_eq :
    rGammaPullbackComparison U K =
      whiskerRight (derivedUnit U K)
          (Hom.moduleGlobalSectionsDerived.{w} (X.localization U)) ≫
        (associator (modulePullbackDerived U K) (modulePushforwardDerived U K)
            (Hom.moduleGlobalSectionsDerived.{w} (X.localization U))).hom ≫
        whiskerLeft (modulePullbackDerived U K) (rGammaDirectImageIso U K).hom :=
  sorry

/-- The component of `rGammaPullbackComparison` at `E` is
`RΓ(X, E) ⟶ RΓ((C / K)_total, La^* E)`. -/
theorem rGammaPullbackComparison_app
    (E : Hom.ModuleDerived.{w} (X.localization U)) :
    (rGammaPullbackComparison U K).app E =
      (Hom.moduleGlobalSectionsDerived.{w} (X.localization U)).map
          ((derivedUnit U K).app E) ≫
        (rGammaDirectImageIso U K).hom.app ((modulePullbackDerived U K).obj E) :=
  sorry

end RingedSite.Hypercovering
