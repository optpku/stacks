/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import stacks_project.Chap85.Lemma_85_18_1_Cartesian

/-!
# Derived adjunction of a hypercovering, modules

If `K` is a hypercovering of the terminal presheaf, the morphism of ringed topoi
`a : (Sh((C / K)_total), O) ⟶ (Sh(C), O_C)` is flat with `O = a⁻¹ O_C`. This leaf
names the unbounded derived functors `La^*` and `Ra_*`, their derived adjunction,
and the canonical unit `E ⟶ Ra_* La^* E`.

The maps `La^*` and `Ra_*` are the ToposHom derived module functors of
`toAmbient`. The derived adjunction is the total-derived pair transport of
`toAmbient.moduleAdjunction`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

-- Homotopy pullback and the derived adjunction use the existing additive law
-- for the specified ringed-topos module pullback.
attribute [local instance] RingedSite.ToposHom.modulePullback_additive

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

-- Reuse the caller's supplied derived pullback witness after activating the
-- canonical additive law for the same module pullback functor.
local instance toAmbient_modulePullback_hasLeftDerived :
    Functor.HasLeftDerivedFunctor
    ((toAmbient K.simplicial).modulePullback.mapHomotopyCategory (up ℤ) ⋙
      Hom.moduleLocalization (site K.simplicial)) (Hom.ModuleQis X) :=
  by
    change ToposHom.HasModulePullbackDerived (toAmbient K.simplicial)
    infer_instance

/-- Module direct image along the ringed augmentation of a hypercovering is additive. -/
noncomputable instance toAmbient_modulePushforward_additive :
    (toAmbient K.simplicial).modulePushforward.Additive :=
  ToposHom.modulePushforward_additive (toAmbient K.simplicial)

/-- Absolute-derived pair conditions for `La^* ⊣ Ra_*` along a hypercovering. -/
abbrev HasModuleDerivedAdjunction : Prop :=
  @Adjunction.TotalDerived.HasPair
    (Hom.ModuleHomotopy.{w} X) (Hom.ModuleHomotopy.{w} (site K.simplicial))
    (Hom.ModuleDerived.{w} X) (Hom.ModuleDerived.{w} (site K.simplicial))
    inferInstance inferInstance inferInstance inferInstance
    ((toAmbient K.simplicial).modulePullback.mapHomotopyCategory (up ℤ))
    ((toAmbient K.simplicial).modulePushforward.mapHomotopyCategory (up ℤ))
    (Hom.ModuleQis.{w} X) (Hom.ModuleQis.{w} (site K.simplicial))
    (Hom.moduleLocalization.{w} X) (Hom.moduleLocalization.{w} (site K.simplicial))
    inferInstance inferInstance inferInstance inferInstance

variable [HasModuleDerivedAdjunction K]

/-- Unbounded derived inverse image `La^*` of `O_C`-modules along the ringed
augmentation of a hypercovering. Because `a` is flat and `O = a⁻¹ O_C`, this
agrees with underived `a^*` and with geometric inverse image `a⁻¹`. -/
abbrev modulePullbackDerived :
    Hom.ModuleDerived.{w} X ⥤ Hom.ModuleDerived.{w} (site K.simplicial) :=
  (toAmbient K.simplicial).modulePullbackDerived

/-- `modulePullbackDerived` is derived module pullback along `toAmbient`. -/
theorem modulePullbackDerived_eq :
    modulePullbackDerived K = (toAmbient K.simplicial).modulePullbackDerived :=
  sorry

/-- Unbounded total right-derived direct image `Ra_*` of `O`-modules along the
ringed augmentation of a hypercovering. -/
abbrev modulePushforwardDerived :
    Hom.ModuleDerived.{w} (site K.simplicial) ⥤ Hom.ModuleDerived.{w} X :=
  (toAmbient K.simplicial).modulePushforwardDerived

/-- `modulePushforwardDerived` is derived module pushforward along `toAmbient`. -/
theorem modulePushforwardDerived_eq :
    modulePushforwardDerived K = (toAmbient K.simplicial).modulePushforwardDerived :=
  sorry

/-- The unbounded derived adjunction `La^* ⊣ Ra_*` attached to a hypercovering. -/
abbrev moduleDerivedAdjunction :
    modulePullbackDerived K ⊣ modulePushforwardDerived K :=
  Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction (toAmbient K.simplicial).moduleAdjunction)
    (Hom.ModuleQis.{w} X) (Hom.ModuleQis.{w} (site K.simplicial))

/-- `moduleDerivedAdjunction` is the total-derived adjunction of the homotopy
transport of `toAmbient.moduleAdjunction`. -/
theorem moduleDerivedAdjunction_eq :
    moduleDerivedAdjunction K =
      Adjunction.TotalDerived.HasPair.derived
        (Adjunction.mapHomotopyCategoryAdjunction
          (toAmbient K.simplicial).moduleAdjunction)
        (Hom.ModuleQis.{w} X) (Hom.ModuleQis.{w} (site K.simplicial)) :=
  sorry

/-- The canonical derived unit `E ⟶ Ra_* La^* E`. -/
abbrev derivedUnit :
    𝟭 (Hom.ModuleDerived.{w} X) ⟶
      modulePullbackDerived K ⋙ modulePushforwardDerived K :=
  (moduleDerivedAdjunction K).unit

/-- `derivedUnit` is the unit of `moduleDerivedAdjunction`. -/
theorem derivedUnit_eq :
    derivedUnit K = (moduleDerivedAdjunction K).unit :=
  sorry

end RingedSite.Localization.AtSimplicialSR
