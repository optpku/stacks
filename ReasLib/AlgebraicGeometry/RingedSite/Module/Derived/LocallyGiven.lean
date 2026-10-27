/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived.LocallyGiven
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization

/-!
# Locally given derived modules on a ringed site

A locally given derived glueing datum on a ringed site `X` consists of a functor
`u : B ⥤ X`, objects `E_U` of `ModuleDerived (X.localization (u.obj U))`, and
restriction isomorphisms `ρ_a` compatible with composition.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open RingedSite
open RingedSite.Hom

noncomputable section

universe u v w z uB vB

namespace RingedSite.ModuleDerived

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, z}]

/-- Chosen derived-category structure on modules over a localization of `X`. -/
instance localizedHasDerivedCategory (U : X) :
    HasDerivedCategory (ModuleCat.{z} (X.localization U)) :=
  localizedModuleCatHasDerivedCategory U

/-- Chosen derived-category structure on modules over `X`. -/
instance hasDerivedCategory : HasDerivedCategory (ModuleCat.{z} X) :=
  moduleCat_hasDerivedCategory X

/-- Restriction of module sheaves along `f : V ⟶ U`, from `X.localization U` to
`X.localization V`. -/
abbrev restriction {U V : X} (f : V ⟶ U) :
    ModuleCat.{z} (X.localization U) ⥤ ModuleCat.{z} (X.localization V) :=
  SheafOfModules.overMap X.structureSheaf f

/-- Continuity of the composite slice functor `Over.map g ⋙ Over.map f`. -/
instance overMap_comp_isContinuous {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    (Over.map g ⋙ Over.map f).IsContinuous
      (X.siteTopology.over W) (X.siteTopology.over U) :=
  Functor.isContinuous_comp (Over.map g) (Over.map f)
    (X.siteTopology.over W) (X.siteTopology.over V) (X.siteTopology.over U)

/-- The ring map underlying `restriction f`. -/
abbrev restrictionRingHom {U V : X} (f : V ⟶ U) :
    X.structureSheaf.over V ⟶
      ((Over.map f).sheafPushforwardContinuous RingCat.{w}
        (X.siteTopology.over V) (X.siteTopology.over U)).obj
        (X.structureSheaf.over U) :=
  SheafOfModules.Derived.restrictionRingHom X.structureSheaf f

/-- Sequential pushforward along `Over.map g` then `Over.map f` is pushforward along
the composite functor. -/
def restrictionCompPushforward {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restriction f ⋙ restriction g ≅
      SheafOfModules.pushforward (F := Over.map g ⋙ Over.map f)
        (restrictionRingHom g ≫
          ((Over.map g).sheafPushforwardContinuous RingCat.{w}
            (X.siteTopology.over W) (X.siteTopology.over V)).map
            (restrictionRingHom f)) :=
  SheafOfModules.Derived.restrictionCompPushforward X.structureSheaf f g

omit [UnivLE.{max u v, z}] in
/-- Ring-map comparison identifying composite slice restriction with sequential
restriction along `Over.map g ⋙ Over.map f`. -/
theorem restriction_comp_ringHom {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionRingHom (g ≫ f) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (Over.mapComp g f).symm.hom RingCat.{w}
          (X.siteTopology.over W) (X.siteTopology.over U)).app
          (X.structureSheaf.over U) =
      restrictionRingHom g ≫
        ((Over.map g).sheafPushforwardContinuous RingCat.{w}
          (X.siteTopology.over W) (X.siteTopology.over V)).map (restrictionRingHom f) :=
  SheafOfModules.Derived.restriction_comp_ringHom X.structureSheaf f g

/-- Sequential restriction along `f` then `g` agrees with restriction along `g ≫ f`. -/
def restrictionComp {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restriction (g ≫ f) ≅ restriction f ⋙ restriction g :=
  SheafOfModules.Derived.restrictionComp X.structureSheaf f g

/-- The bundled exact functor underlying slice restriction. -/
abbrev restrictionExact {U V : X} (f : V ⟶ U) :
    ModuleCat.{z} (X.localization U) ⥤ₑ ModuleCat.{z} (X.localization V) :=
  SheafOfModules.Derived.restrictionExact X.structureSheaf f

/-- Exact-functor isomorphism underlying `restrictionComp`. -/
def restrictionCompExactIso {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionExact (g ≫ f) ≅ (restrictionExact f).comp (restrictionExact g) :=
  SheafOfModules.Derived.restrictionCompExactIso X.structureSheaf f g

/-- The exact derived functor induced by restriction along `f : V ⟶ U`. -/
def restrictionDerived {U V : X} (f : V ⟶ U) :
    ModuleDerived.{z} (X.localization U) ⥤ ModuleDerived.{z} (X.localization V) :=
  SheafOfModules.Derived.restrictionDerived X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) f

/-- Reidentification of derived restriction along equal arrows of `X`. -/
def restrictionDerivedCongr {U V : X} {f g : V ⟶ U} (h : f = g) :
    restrictionDerived f ≅ restrictionDerived g :=
  SheafOfModules.Derived.restrictionDerivedCongr X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) h

/-- Derived-level composition comparison
`restrictionDerived (g ≫ f) ≅ restrictionDerived f ⋙ restrictionDerived g`. -/
def restrictionCompIso {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionDerived (g ≫ f) ≅ restrictionDerived f ⋙ restrictionDerived g :=
  SheafOfModules.Derived.restrictionCompIso X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) f g

/-- Direct restriction from `X` to `X.localization V` agrees with restriction to
`X.localization U` followed by slice restriction along `f : V ⟶ U`. -/
def restrictionIteratedIso {U V : X} (f : V ⟶ U) :
    localizedRestriction.{z} X U ⋙ restriction f ≅ localizedRestriction.{z} X V :=
  SheafOfModules.Derived.restrictionIteratedIso X.structureSheaf f

/-- The bundled exact functor underlying ambient restriction to a localization. -/
abbrev localizedRestrictionExact (U : X) :
    ModuleCat.{z} X ⥤ₑ ModuleCat.{z} (X.localization U) :=
  SheafOfModules.Derived.localizedRestrictionExact X.structureSheaf U

/-- Exact-functor isomorphism underlying `restrictionIteratedIso`. -/
def restrictionIteratedExactIso {U V : X} (f : V ⟶ U) :
    (localizedRestrictionExact U).comp (restrictionExact f) ≅ localizedRestrictionExact V :=
  SheafOfModules.Derived.restrictionIteratedExactIso X.structureSheaf f

/-- Derived-level iterated-vs-direct comparison
`localizedRestrictionDerived X U ⋙ restrictionDerived f ≅ localizedRestrictionDerived X V`. -/
def restrictionDerivedIteratedIso {U V : X} (f : V ⟶ U) :
    localizedRestrictionDerived.{z} X U ⋙ restrictionDerived f ≅
      localizedRestrictionDerived.{z} X V :=
  SheafOfModules.Derived.restrictionDerivedIteratedIso X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) (abelian := moduleCatAbelian X) f

/-- A locally given derived glueing datum on a ringed site: a functor `u : B ⥤ X`,
objects `E_U` of `ModuleDerived (X.localization (u.obj U))`, and restriction
isomorphisms `ρ_a` compatible with composition. -/
abbrev LocallyGiven (X : RingedSite.{u, v, w})
    (B : Type uB) [Category.{vB} B] :=
  SheafOfModules.Derived.LocallyGiven X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) B

variable {B : Type uB} [Category.{vB} B]

/-- The composition cocycle of a locally given datum. -/
theorem spec (D : LocallyGiven X B) {W V U : B} (a : V ⟶ U) (b : W ⟶ V) :
    ((restrictionCompIso (D.u.map a) (D.u.map b)).symm ≪≫
        restrictionDerivedCongr (D.u.map_comp b a).symm).app (D.obj U) ≪≫
      D.iso (b ≫ a) =
    (restrictionDerived (D.u.map b)).mapIso (D.iso a) ≪≫ D.iso b :=
  SheafOfModules.Derived.spec X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) D a b

/-- The tautological locally given datum attached to a global object `E` of
`ModuleDerived X`, with `u = 𝟭` and `E_U = j[U]⁻¹ E`. -/
def ofGlobal (E : ModuleDerived.{z} X) : LocallyGiven X X :=
  SheafOfModules.Derived.ofGlobal X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) (abelian := moduleCatAbelian X) E

/-- Identity-arrow computation for the tautological locally given datum. -/
theorem ofGlobal_iso_id (E : ModuleDerived.{z} X) (U : X) :
    ((ofGlobal E).iso (𝟙 U)).hom =
      (restrictionDerivedIteratedIso (𝟙 U)).hom.app E :=
  SheafOfModules.Derived.ofGlobal_iso_id X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) (abelian := moduleCatAbelian X) E U

/-- A solution of a locally given derived datum is a global object `E` of
`ModuleDerived X` with isomorphisms `ρ_U : E |_{X.localization (u.obj U)} ≅ E_U`
compatible with the given `ρ_a`. -/
abbrev Solution {X : RingedSite.{u, v, w}}
    {B : Type uB} [Category.{vB} B] (D : LocallyGiven X B) :=
  SheafOfModules.Derived.Solution X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) (abelian := moduleCatAbelian X) D

/-- The tautological solution of `ofGlobal E`. -/
def Solution.ofGlobal (E : ModuleDerived.{z} X) : Solution (ofGlobal E) :=
  SheafOfModules.Derived.Solution.ofGlobal X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) (abelian := moduleCatAbelian X) E

/-- The global object of the tautological solution is the original object. -/
theorem Solution.ofGlobal_obj (E : ModuleDerived.{z} X) :
    (Solution.ofGlobal E).obj = E :=
  SheafOfModules.Derived.Solution.ofGlobal_obj X.structureSheaf
    (abelianOver := fun U => localizedModuleCatAbelian U) (abelian := moduleCatAbelian X) E

end RingedSite.ModuleDerived
