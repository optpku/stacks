/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_20_2_Adjunction

/-!
# Lemma 85.20.2

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings, and let `K` be a hypercovering of `X`. For every `E` in
`D(O_X)`, the canonical derived-unit map `E ⟶ Ra_* La^* E` is an isomorphism.
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

/-- Lemma 85.20.2: Let `C` be a site with fibre products and `X` an object of
`C`. Let `O_C` be a sheaf of rings. Let `K` be a hypercovering of `X`. For
`E ∈ D(O_X)` the map `E ⟶ Ra_* La^* E` is an isomorphism. -/
@[stacks 0DA5]
theorem derivedUnit_app_isIso (E : Hom.ModuleDerived.{w} (X.localization U)) :
    IsIso ((derivedUnit U K).app E :
      E ⟶ (modulePushforwardDerived U K).obj ((modulePullbackDerived U K).obj E)) :=
  sorry

/-- The derived unit `𝟭 ⟶ La^* ⋙ Ra_*` is an isomorphism of functors on `D(O_X)`. -/
theorem derivedUnit_isIso : IsIso (derivedUnit U K) :=
  sorry

end RingedSite.Hypercovering
