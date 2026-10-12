/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import stacks_project.Chap85.Lemma_85_18_2_Adjunction
public import stacks_project.Chap85.Lemma_85_19_1_Slice

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

/-- `site_terminal` is `site` of the underlying simplicial object. -/
theorem site_terminal_eq :
    site_terminal Y L = site L.simplicial :=
  sorry

/-- The ringed augmentation `a` of a site-level hypercovering, with the ambient
ringed site explicit. -/
abbrev toAmbient_terminal : ToposHom (site L.simplicial) Y :=
  toAmbient L.simplicial

/-- `toAmbient_terminal` is `toAmbient` of the underlying simplicial object. -/
theorem toAmbient_terminal_eq :
    toAmbient_terminal Y L = toAmbient L.simplicial :=
  sorry

/-- Unbounded derived inverse image `La^*` along a site-level hypercovering, with
the ambient ringed site explicit. -/
abbrev modulePullbackDerived_terminal :
    Hom.ModuleDerived.{w} Y ⥤ Hom.ModuleDerived.{w} (site L.simplicial) :=
  (toAmbient L.simplicial).modulePullbackDerived

/-- `modulePullbackDerived_terminal` is derived module pullback along
`toAmbient_terminal`. -/
theorem modulePullbackDerived_terminal_eq :
    modulePullbackDerived_terminal Y L = (toAmbient L.simplicial).modulePullbackDerived :=
  sorry

/-- Unbounded total right-derived direct image `Ra_*` along a site-level
hypercovering, with the ambient ringed site explicit. -/
abbrev modulePushforwardDerived_terminal :
    Hom.ModuleDerived.{w} (site L.simplicial) ⥤ Hom.ModuleDerived.{w} Y :=
  (toAmbient L.simplicial).modulePushforwardDerived

/-- `modulePushforwardDerived_terminal` is derived module pushforward along
`toAmbient_terminal`. -/
theorem modulePushforwardDerived_terminal_eq :
    modulePushforwardDerived_terminal Y L =
      (toAmbient L.simplicial).modulePushforwardDerived :=
  sorry

/-- Absolute-derived pair conditions for `La^* ⊣ Ra_*` along a site-level
hypercovering, with the ambient ringed site explicit. -/
abbrev HasModuleDerivedAdjunction_terminal : Prop :=
  HasModuleDerivedAdjunction L

variable [HasModuleDerivedAdjunction_terminal Y L]

/-- The unbounded derived adjunction `La^* ⊣ Ra_*` of a site-level hypercovering,
with the ambient ringed site explicit. -/
abbrev moduleDerivedAdjunction_terminal :
    modulePullbackDerived_terminal Y L ⊣ modulePushforwardDerived_terminal Y L :=
  moduleDerivedAdjunction L

/-- `moduleDerivedAdjunction_terminal` is the terminal-hypercovering derived
adjunction. -/
theorem moduleDerivedAdjunction_terminal_eq :
    moduleDerivedAdjunction_terminal Y L = moduleDerivedAdjunction L :=
  sorry

/-- The canonical derived unit `E ⟶ Ra_* La^* E`, with the ambient ringed site
explicit. -/
abbrev derivedUnit_terminal :
    𝟭 (Hom.ModuleDerived.{w} Y) ⟶
      modulePullbackDerived_terminal Y L ⋙ modulePushforwardDerived_terminal Y L :=
  derivedUnit L

/-- `derivedUnit_terminal` is the terminal-hypercovering derived unit. -/
theorem derivedUnit_terminal_eq :
    derivedUnit_terminal Y L = derivedUnit L :=
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

/-- Unbounded derived inverse image `La^*` of `O_U`-modules along the ringed
augmentation of a hypercovering of an object. -/
abbrev modulePullbackDerived :
    Hom.ModuleDerived.{w} (X.localization U) ⥤
      Hom.ModuleDerived.{w}
        (site_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)) :=
  modulePullbackDerived_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- `modulePullbackDerived` is the slice instantiation of
`modulePullbackDerived_terminal`. -/
theorem modulePullbackDerived_eq :
    modulePullbackDerived U K =
      modulePullbackDerived_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- Unbounded total right-derived direct image `Ra_*` of `O`-modules along the
ringed augmentation of a hypercovering of an object. -/
abbrev modulePushforwardDerived :
    Hom.ModuleDerived.{w}
        (site_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)) ⥤
      Hom.ModuleDerived.{w} (X.localization U) :=
  modulePushforwardDerived_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- `modulePushforwardDerived` is the slice instantiation of
`modulePushforwardDerived_terminal`. -/
theorem modulePushforwardDerived_eq :
    modulePushforwardDerived U K =
      modulePushforwardDerived_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- Absolute-derived pair conditions for `La^* ⊣ Ra_*` along a hypercovering of an
object. -/
abbrev HasModuleDerivedAdjunction : Prop :=
  HasModuleDerivedAdjunction_terminal (X.localization U)
    (toSliceTerminal X.siteTopology U K)

variable [HasModuleDerivedAdjunction U K]

/-- The unbounded derived adjunction `La^* ⊣ Ra_*` attached to a hypercovering of an
object. -/
abbrev moduleDerivedAdjunction :
    modulePullbackDerived U K ⊣ modulePushforwardDerived U K :=
  moduleDerivedAdjunction_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- `moduleDerivedAdjunction` is the slice instantiation of
`moduleDerivedAdjunction_terminal`. -/
theorem moduleDerivedAdjunction_eq :
    moduleDerivedAdjunction U K =
      moduleDerivedAdjunction_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- The canonical derived unit `E ⟶ Ra_* La^* E` on `D(O_U)`. -/
abbrev derivedUnit :
    𝟭 (Hom.ModuleDerived.{w} (X.localization U)) ⟶
      modulePullbackDerived U K ⋙ modulePushforwardDerived U K :=
  derivedUnit_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- `derivedUnit` is the slice instantiation of `derivedUnit_terminal`. -/
theorem derivedUnit_eq :
    derivedUnit U K =
      derivedUnit_terminal (X.localization U) (toSliceTerminal X.siteTopology U K) :=
  sorry

end RingedSite.Hypercovering
