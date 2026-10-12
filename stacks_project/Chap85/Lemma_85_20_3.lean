/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_20_3_Comparison

/-!
# Lemma 85.20.3

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings, and let `K` be a hypercovering of `X`. Then there is a canonical
isomorphism `RΓ(X, E) ≅ RΓ((C / K)_total, La^* E)` in `D(Ab)` for every `E` in
`D(O_X)`, where `RΓ(X, -)` is derived global sections on `C / X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)

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

/-- Lemma 85.20.3: Let `C` be a site with fibre products and `X` an object of
`C`. Let `O_C` be a sheaf of rings. Let `K` be a hypercovering of `X`. For
`E ∈ D(O_X)` the canonical map `RΓ(X, E) ⟶ RΓ((C / K)_total, La^* E)` is an
isomorphism. -/
@[stacks 0DA6]
theorem rGammaPullbackComparison_app_isIso
    (E : Hom.ModuleDerived.{w} (X.localization U)) :
    IsIso ((rGammaPullbackComparison U K).app E) :=
  sorry

/-- The comparison `RΓ(X, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)` is an isomorphism of
functors. -/
theorem rGammaPullbackComparison_isIso :
    IsIso (rGammaPullbackComparison U K) :=
  sorry

end RingedSite.Hypercovering
