/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedModuleDescent
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

/- Lemma 85.20.2: For every object of the unbounded derived category of
module sheaves on `X.localization U`, the canonical derived unit of a
hypercovering of `U` is invertible. -/
@[stacks 0DA5] #check
  (RingedSite.Localization.AtSimplicialSR.derivedUnit_app_isIso
    (X := X.localization U) (toSliceTerminal X.siteTopology U K) :
    ∀ E : Hom.ModuleDerived.{w} (X.localization U),
      IsIso ((RingedSite.Hypercovering.derivedUnit U K).app E))

#check
  (RingedSite.Localization.AtSimplicialSR.derivedUnit_isIso
    (X := X.localization U) (toSliceTerminal X.siteTopology U K) :
    IsIso (RingedSite.Hypercovering.derivedUnit U K))

end RingedSite.Hypercovering
