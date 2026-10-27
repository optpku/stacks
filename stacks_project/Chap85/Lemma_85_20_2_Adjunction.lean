/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.DerivedAdjunction

/-!
# Derived adjunction of a hypercovering of an object, modules

If `K` is a hypercovering of an object `U`, the morphism of ringed topoi
`a : (Sh((C / K)_total), O) ⟶ (Sh(C / U), O_U)` is the slice instantiation of
the terminal-hypercovering augmentation. This leaf names the unbounded derived
functors `La^*` and `Ra_*`, their derived adjunction, and the canonical unit
`E ⟶ Ra_* La^* E` on `D(O_U)`.
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

section Terminal

open Localization.AtSimplicialSR

variable (Y : RingedSite.{u, v, w})
variable [h_eq : HasEqualizers Y.carrier] [h_pbY : HasPullbacks Y.carrier]
include h_eq h_pbY
variable (L : HypercoveringOf.Terminal.{ι} Y.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
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

/-- The ringed site `((C / L)_total, O)`, with the ambient ringed site explicit. -/
abbrev site_terminal : RingedSite.{max ι u v, max ι u v, w} :=
  site L.simplicial

/-- The ringed augmentation `a` of a site-level hypercovering, with the ambient
ringed site explicit. -/
abbrev toAmbient_terminal : ToposHom (site L.simplicial) Y :=
  toAmbient L.simplicial

/-- Unbounded derived inverse image `La^*` along a site-level hypercovering, with
the ambient ringed site explicit. -/
abbrev modulePullbackDerived_terminal :
    Hom.ModuleDerived.{w} Y ⥤ Hom.ModuleDerived.{w} (site L.simplicial) :=
  (toAmbient L.simplicial).modulePullbackDerived

/-- Unbounded total right-derived direct image `Ra_*` along a site-level
hypercovering, with the ambient ringed site explicit. -/
abbrev modulePushforwardDerived_terminal :
    Hom.ModuleDerived.{w} (site L.simplicial) ⥤ Hom.ModuleDerived.{w} Y :=
  (toAmbient L.simplicial).modulePushforwardDerived

/-- Absolute-derived pair conditions for `La^* ⊣ Ra_*` along a site-level
hypercovering, with the ambient ringed site explicit. -/
abbrev HasModuleDerivedAdjunction_terminal : Prop :=
  ToposHom.HasModuleDerivedAdjunction (toAmbient L.simplicial)

variable [HasModuleDerivedAdjunction_terminal Y L]

/-- The unbounded derived adjunction `La^* ⊣ Ra_*` of a site-level hypercovering,
with the ambient ringed site explicit. -/
abbrev moduleDerivedAdjunction_terminal :
    modulePullbackDerived_terminal Y L ⊣ modulePushforwardDerived_terminal Y L :=
  (toAmbient L.simplicial).moduleDerivedAdjunction

/-- The canonical derived unit `E ⟶ Ra_* La^* E`, with the ambient ringed site
explicit. -/
abbrev derivedUnit_terminal :
    𝟭 (Hom.ModuleDerived.{w} Y) ⟶
      modulePullbackDerived_terminal Y L ⋙ modulePushforwardDerived_terminal Y L :=
  Localization.AtSimplicialSR.derivedUnit L

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

/-- Absolute-derived pair conditions for `La^* ⊣ Ra_*` along a hypercovering of an
object. -/
abbrev HasModuleDerivedAdjunction : Prop :=
  HasModuleDerivedAdjunction_terminal (X.localization U)
    (toSliceTerminal X.siteTopology U K)

end RingedSite.Hypercovering
