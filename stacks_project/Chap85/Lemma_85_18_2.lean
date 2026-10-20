/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_18_2_Adjunction

/-!
# Lemma 85.18.2

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of
rings, and let `K` be a hypercovering. For every `E` in `D(O_C)`, the canonical
derived-unit map `E ⟶ Ra_* La^* E` is an isomorphism.
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

/-- Lemma 85.18.2: Let `C` be a site with equalizers and fibre products. Let `O_C`
be a sheaf of rings. Let `K` be a hypercovering. For `E ∈ D(O_C)` the map
`E ⟶ Ra_* La^* E` is an isomorphism. -/
@[stacks 0DA0]
theorem derivedUnit_app_isIso (E : Hom.ModuleDerived.{w} X) :
    IsIso ((derivedUnit K).app E) :=
  sorry

/-- The derived unit `𝟭 ⟶ La^* ⋙ Ra_*` is an isomorphism of functors on `D(O_C)`. -/
theorem derivedUnit_isIso : IsIso (derivedUnit K) :=
  sorry

end RingedSite.Localization.AtSimplicialSR
