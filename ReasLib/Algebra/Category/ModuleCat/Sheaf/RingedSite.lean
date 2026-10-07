module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.Linear
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import Mathlib.Tactic.CrossRefAttribute

/-! # Modules on a Ringed Site

This module supplies the canonical aliases and change-of-scalars functors for modules over a
commutative ring sheaf on an arbitrary site.  It is independent of any particular geometric
category of spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite

/-- The category of sheaves of modules over a commutative ring sheaf on a site. -/
@[stacks 03CW "commutative ringed-site modules"]
abbrev ringedSiteModuleCategory.{uC, vC, zM, wR}
    {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{wR} RingCat.{wR})]
    (𝒪 : Sheaf J CommRingCat.{wR}) :=
  SheafOfModules.{zM} (CategoryTheory.Sheaf.ringSheafOfComm 𝒪)

/-- A commutative ring sheaf, viewed through its underlying ring sheaf. -/
abbrev ringSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (𝒪 : Sheaf J CommRingCat.{w}) :=
  CategoryTheory.Sheaf.ringSheafOfComm 𝒪

/-- The underlying ring-sheaf morphism induced by a morphism of commutative ring sheaves. -/
abbrev ringSheafMap {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {𝒪 𝒪' : Sheaf J CommRingCat.{w}} (α : 𝒪 ⟶ 𝒪') :
    ringSheaf J 𝒪 ⟶ ringSheaf J 𝒪' :=
  CategoryTheory.Sheaf.ringSheafOfCommMap α

/-- The same-site structure morphism written with an identity pushforward target. -/
abbrev ringedSiteStructureMap {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {𝒪 𝒪' : Sheaf J CommRingCat.{w}} (α : 𝒪 ⟶ 𝒪') :
    ringSheaf J 𝒪 ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J J).obj
      (ringSheaf J 𝒪') :=
  ringSheafMap α ≫
    (Functor.sheafPushforwardContinuousId RingCat.{w} J).inv.app (ringSheaf J 𝒪')

/-- Restriction of scalars along a morphism of commutative ring sheaves on one site. -/
abbrev restrictionAlong.{uC, vC, wR, zM}
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{wR} RingCat.{wR})]
    {𝒪 𝒪' : Sheaf J CommRingCat.{wR}} (α : 𝒪 ⟶ 𝒪') :
    ringedSiteModuleCategory.{uC, vC, zM, wR} J 𝒪' ⥤
      ringedSiteModuleCategory.{uC, vC, zM, wR} J 𝒪 :=
  SheafOfModules.restrictScalars (ringSheafMap α)

/-- The structure ring sheaf, regarded as a module over itself. -/
abbrev unitModule {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (𝒪 : Sheaf J CommRingCat.{w}) :
    ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.unit (ringSheaf J 𝒪)

end SheafOfModules.RingedSite
