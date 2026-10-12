/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_18_3_Comparison

/-!
# Lemma 85.18.3

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of
rings, and let `K` be a hypercovering. For every `E` in `D(O_C)` there is a
canonical isomorphism `RΓ(C, E) ≅ RΓ((C / K)_total, La^* E)` in `D(Ab)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
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

/-- Lemma 85.18.3: Let `C` be a site with equalizers and fibre products. Let `O_C`
be a sheaf of rings. Let `K` be a hypercovering. For `E ∈ D(O_C)` the canonical map
`RΓ(C, E) ⟶ RΓ((C / K)_total, La^* E)` is an isomorphism. -/
@[stacks 0DA1]
theorem rGammaPullbackComparison_app_isIso (E : Hom.ModuleDerived.{w} X) :
    IsIso ((rGammaPullbackComparison K).app E) :=
  sorry

/-- The comparison `RΓ(C, -) ⟶ La^* ⋙ RΓ((C / K)_total, -)` is an isomorphism of functors. -/
theorem rGammaPullbackComparison_isIso : IsIso (rGammaPullbackComparison K) :=
  sorry

end RingedSite.Localization.AtSimplicialSR
