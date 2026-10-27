/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedAdjunction

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

/-- Module direct image along the ringed augmentation of a hypercovering is additive. -/
theorem toAmbient_modulePushforward_additive :
    (toAmbient K.simplicial).modulePushforward.Additive :=
  ToposHom.modulePushforward_additive (toAmbient K.simplicial)

/-- Absolute-derived pair conditions for `La^* ⊣ Ra_*` along a hypercovering. -/
abbrev HasModuleDerivedAdjunction : Prop :=
  ToposHom.HasModuleDerivedAdjunction (toAmbient K.simplicial)

variable [HasModuleDerivedAdjunction K]

/-- Unbounded derived inverse image `La^*` of `O_C`-modules along the ringed
augmentation of a hypercovering. Because `a` is flat and `O = a⁻¹ O_C`, this
agrees with underived `a^*` and with geometric inverse image `a⁻¹`. -/
abbrev modulePullbackDerived :
    Hom.ModuleDerived.{w} X ⥤ Hom.ModuleDerived.{w} (site K.simplicial) :=
  (toAmbient K.simplicial).modulePullbackDerived

/-- Unbounded total right-derived direct image `Ra_*` of `O`-modules along the
ringed augmentation of a hypercovering. -/
abbrev modulePushforwardDerived :
    Hom.ModuleDerived.{w} (site K.simplicial) ⥤ Hom.ModuleDerived.{w} X :=
  (toAmbient K.simplicial).modulePushforwardDerived

/-- The unbounded derived adjunction `La^* ⊣ Ra_*` attached to a hypercovering. -/
abbrev moduleDerivedAdjunction :
    modulePullbackDerived K ⊣ modulePushforwardDerived K :=
  (toAmbient K.simplicial).moduleDerivedAdjunction

#check (RingedSite.Localization.AtSimplicialSR.derivedUnit K :
  𝟭 (Hom.ModuleDerived.{w} X) ⟶ modulePullbackDerived K ⋙ modulePushforwardDerived K)

end RingedSite.Localization.AtSimplicialSR
