module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular meromorphic sections

A section after extension of scalars is regular when the induced morphism from the target unit
module is a monomorphism. This file exposes the general same-site construction and its
meromorphic-section specialization.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}

/-- The morphism from the target unit module to the pullback of `ℱ` induced by a global section of
that pullback. -/
abbrev pullbackSectionMap
    (α : 𝒪 ⟶ 𝒪') (ℱ : ringedSiteModuleCategory J 𝒪)
    [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
    (s : ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).sections) :
    unitModule J 𝒪' ⟶ (SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ :=
  ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).unitHomEquiv.symm s

/-- A section of the pullback of `ℱ` along `α` is regular when its induced unit-module morphism
is a monomorphism. -/
abbrev IsRegularSection
    (α : 𝒪 ⟶ 𝒪') (ℱ : ringedSiteModuleCategory J 𝒪)
    [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
    (s : ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).sections) : Prop :=
  Mono (pullbackSectionMap α ℱ s)

/-- The regular-section condition is the mono condition on the induced unit-module morphism. -/
theorem isRegularSection_iff_mono
    (α : 𝒪 ⟶ 𝒪') (ℱ : ringedSiteModuleCategory J 𝒪)
    [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
    (s : ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).sections) :
    IsRegularSection α ℱ s ↔ Mono (pullbackSectionMap α ℱ s) :=
  Iff.rfl

end SheafOfModules.RingedSite

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The morphism `𝒦_X ⟶ 𝒦_X(ℱ)` induced by a meromorphic section of `ℱ`. -/
@[stacks 02OX "morphism induced by a meromorphic section"]
abbrev meromorphicSectionMap
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪)
    (s : X.meromorphicSections ℱ) :
    (unitModule (Opens.grothendieckTopology X.toTopCat) (meromorphicFunctionSheaf X) :
      ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
        (meromorphicFunctionSheaf X)) ⟶ X.meromorphicSectionSheaf ℱ :=
  SheafOfModules.RingedSite.pullbackSectionMap X.toMeromorphicFunctionSheafHom ℱ s

/-- A meromorphic section is regular when its induced map
`𝒦_X ⟶ 𝒦_X(ℱ)` is a monomorphism. -/
@[stacks 02OX]
abbrev IsRegularMeromorphicSection
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪)
    (s : X.meromorphicSections ℱ) : Prop :=
  SheafOfModules.RingedSite.IsRegularSection X.toMeromorphicFunctionSheafHom ℱ s

/-- A meromorphic section is regular exactly when its induced morphism is a monomorphism. -/
theorem isRegularMeromorphicSection_iff_mono
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪)
    (s : X.meromorphicSections ℱ) :
    IsRegularMeromorphicSection X ℱ s ↔ Mono (X.meromorphicSectionMap ℱ s) :=
  SheafOfModules.RingedSite.isRegularSection_iff_mono X.toMeromorphicFunctionSheafHom ℱ s

end AlgebraicGeometry.LocallyRingedSpace
