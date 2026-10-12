/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.CategoryTheory.Functor.Exactness.Identity

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

/-- Slice restriction of module sheaves is additive. -/
instance restriction_additive {U V : X} (f : V ⟶ U) : (restriction f).Additive := sorry

/-- Restriction along a slice arrow preserves finite limits. -/
instance restriction_preservesFiniteLimits {U V : X} (f : V ⟶ U) :
    PreservesFiniteLimits (restriction f) := sorry

/-- Restriction along a slice arrow preserves finite colimits. -/
instance restriction_preservesFiniteColimits {U V : X} (f : V ⟶ U) :
    PreservesFiniteColimits (restriction f) := sorry

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
  (Sheaf.pushforwardOverMapIso X.structureSheaf f).inv

/-- Sequential pushforward along `Over.map g` then `Over.map f` is pushforward along
the composite functor. -/
def restrictionCompPushforward {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restriction f ⋙ restriction g ≅
      SheafOfModules.pushforward (F := Over.map g ⋙ Over.map f)
        (restrictionRingHom g ≫
          ((Over.map g).sheafPushforwardContinuous RingCat.{w}
            (X.siteTopology.over W) (X.siteTopology.over V)).map
            (restrictionRingHom f)) :=
  SheafOfModules.pushforwardComp (restrictionRingHom g) (restrictionRingHom f)

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
          (X.siteTopology.over W) (X.siteTopology.over V)).map (restrictionRingHom f) := sorry

/-- Sequential restriction along `f` then `g` agrees with restriction along `g ≫ f`. -/
def restrictionComp {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restriction (g ≫ f) ≅ restriction f ⋙ restriction g :=
  SheafOfModules.pushforwardCongr₂ (restrictionRingHom (g ≫ f)) (Over.mapComp g f).symm
      (restriction_comp_ringHom f g) ≪≫
    (restrictionCompPushforward f g).symm

/-- The bundled exact functor underlying slice restriction. -/
abbrev restrictionExact {U V : X} (f : V ⟶ U) :
    ModuleCat.{z} (X.localization U) ⥤ₑ ModuleCat.{z} (X.localization V) :=
  ExactFunctor.of (restriction f)

/-- Exact-functor isomorphism underlying `restrictionComp`. -/
def restrictionCompExactIso {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionExact (g ≫ f) ≅ (restrictionExact f).comp (restrictionExact g) :=
  ObjectProperty.isoMk (exactFunctor _ _) (restrictionComp f g)

/-- The exact derived functor induced by restriction along `f : V ⟶ U`. -/
def restrictionDerived {U V : X} (f : V ⟶ U) :
    ModuleDerived.{z} (X.localization U) ⥤ ModuleDerived.{z} (X.localization V) :=
  (restriction f).mapDerivedCategory

/-- Reidentification of derived restriction along equal arrows of `X`. -/
def restrictionDerivedCongr {U V : X} {f g : V ⟶ U} (h : f = g) :
    restrictionDerived f ≅ restrictionDerived g :=
  eqToIso (congrArg restrictionDerived h)

/-- Derived-level composition comparison
`restrictionDerived (g ≫ f) ≅ restrictionDerived f ⋙ restrictionDerived g`. -/
def restrictionCompIso {U V W : X} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionDerived (g ≫ f) ≅ restrictionDerived f ⋙ restrictionDerived g :=
  ExactFunctor.MapDerivedCategory.mapIso (restrictionCompExactIso f g) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso (restrictionExact f) (restrictionExact g)

/-- Direct restriction from `X` to `X.localization V` agrees with restriction to
`X.localization U` followed by slice restriction along `f : V ⟶ U`. -/
def restrictionIteratedIso {U V : X} (f : V ⟶ U) :
    localizedRestriction.{z} X U ⋙ restriction f ≅ localizedRestriction.{z} X V :=
  SheafOfModules.overFunctorMap X.structureSheaf f

/-- Additivity of ambient restriction to a localization. -/
instance localizedRestriction_additiveInst (U : X) :
    (localizedRestriction.{z} X U).Additive :=
  localizedRestriction_additive X U

/-- Finite-limit preservation for ambient restriction to a localization. -/
instance localizedRestriction_preservesFiniteLimitsInst (U : X) :
    PreservesFiniteLimits (localizedRestriction.{z} X U) :=
  localizedRestriction_preservesFiniteLimits X U

/-- Finite-colimit preservation for ambient restriction to a localization. -/
instance localizedRestriction_preservesFiniteColimitsInst (U : X) :
    PreservesFiniteColimits (localizedRestriction.{z} X U) :=
  localizedRestriction_preservesFiniteColimits X U

/-- The bundled exact functor underlying ambient restriction to a localization. -/
abbrev localizedRestrictionExact (U : X) :
    ModuleCat.{z} X ⥤ₑ ModuleCat.{z} (X.localization U) :=
  ExactFunctor.of (localizedRestriction.{z} X U)

/-- Exact-functor isomorphism underlying `restrictionIteratedIso`. -/
def restrictionIteratedExactIso {U V : X} (f : V ⟶ U) :
    (localizedRestrictionExact U).comp (restrictionExact f) ≅ localizedRestrictionExact V :=
  ObjectProperty.isoMk (exactFunctor _ _) (restrictionIteratedIso f)

/-- Derived-level iterated-vs-direct comparison
`localizedRestrictionDerived X U ⋙ restrictionDerived f ≅ localizedRestrictionDerived X V`. -/
def restrictionDerivedIteratedIso {U V : X} (f : V ⟶ U) :
    localizedRestrictionDerived.{z} X U ⋙ restrictionDerived f ≅
      localizedRestrictionDerived.{z} X V :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (localizedRestrictionExact U) (restrictionExact f)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso (restrictionIteratedExactIso f)

/-- A locally given derived glueing datum on a ringed site: a functor `u : B ⥤ X`,
objects `E_U` of `ModuleDerived (X.localization (u.obj U))`, and restriction
isomorphisms `ρ_a` compatible with composition. -/
@[stacks 0DC9]
structure LocallyGiven (X : RingedSite.{u, v, w}) (B : Type uB) [Category.{vB} B]
    [UnivLE.{max u v, z}] where
  /-- The indexing functor `u : B ⥤ X`. -/
  u : B ⥤ X
  /-- The object `E_U` of `ModuleDerived (X.localization (u.obj U))`. -/
  obj (U : B) : ModuleDerived.{z} (X.localization (u.obj U))
  /-- The restriction isomorphism `ρ_a : E_U |_{X.localization (u.obj V)} ≅ E_V`. -/
  iso {V U : B} (a : V ⟶ U) :
    (restrictionDerived (u.map a)).obj (obj U) ≅ obj V
  /-- Composition cocycle: `ρ_{b ≫ a}` agrees with `ρ_b ∘ ρ_a` after
  `restrictionCompIso`. -/
  iso_comp {W V U : B} (a : V ⟶ U) (b : W ⟶ V) :
      ((restrictionCompIso (u.map a) (u.map b)).symm ≪≫
          restrictionDerivedCongr (u.map_comp b a).symm).app (obj U) ≪≫
        iso (b ≫ a) =
      (restrictionDerived (u.map b)).mapIso (iso a) ≪≫ iso b

variable {B : Type uB} [Category.{vB} B]

/-- The transition isomorphism `ρ_a` of a locally given datum. -/
def iso_apply (D : LocallyGiven X B) {V U : B} (a : V ⟶ U) :
    (restrictionDerived (D.u.map a)).obj (D.obj U) ≅ D.obj V :=
  D.iso a

/-- The composition cocycle of a locally given datum. -/
theorem spec (D : LocallyGiven X B) {W V U : B} (a : V ⟶ U) (b : W ⟶ V) :
    ((restrictionCompIso (D.u.map a) (D.u.map b)).symm ≪≫
        restrictionDerivedCongr (D.u.map_comp b a).symm).app (D.obj U) ≪≫
      D.iso (b ≫ a) =
    (restrictionDerived (D.u.map b)).mapIso (D.iso a) ≪≫ D.iso b := sorry

/-- The tautological locally given datum attached to a global object `E` of
`ModuleDerived X`, with `u = 𝟭` and `E_U = j[U]⁻¹ E`. -/
def ofGlobal (E : ModuleDerived.{z} X) : LocallyGiven X X where
  u := 𝟭 X
  obj U := (localizedRestrictionDerived.{z} X U).obj E
  iso a := (restrictionDerivedIteratedIso a).app E
  iso_comp := sorry

/-- Identity-arrow computation for the tautological locally given datum. -/
theorem ofGlobal_iso_id (E : ModuleDerived.{z} X) (U : X) :
    ((ofGlobal E).iso (𝟙 U)).hom =
      (restrictionDerivedIteratedIso (𝟙 U)).hom.app E := sorry

/-- A solution of a locally given derived datum is a global object `E` of
`ModuleDerived X` with isomorphisms `ρ_U : E |_{X.localization (u.obj U)} ≅ E_U`
compatible with the given `ρ_a`. -/
structure Solution {X : RingedSite.{u, v, w}} {B : Type uB} [Category.{vB} B]
    [UnivLE.{max u v, z}] (D : LocallyGiven X B) where
  /-- The global object `E` of `ModuleDerived X`. -/
  obj : ModuleDerived.{z} X
  /-- The isomorphism `ρ_U : E |_{X.localization (u.obj U)} ≅ E_U`. -/
  iso (U : B) :
    (localizedRestrictionDerived.{z} X (D.u.obj U)).obj obj ≅ D.obj U
  /-- Compatibility `ρ_a ∘ ρ_U |_{X.localization (u.obj V)} = ρ_V`. -/
  iso_comp {V U : B} (a : V ⟶ U) :
      (restrictionDerived (D.u.map a)).map (iso U).hom ≫ (D.iso a).hom =
        (restrictionDerivedIteratedIso (D.u.map a)).hom.app obj ≫ (iso V).hom

/-- The tautological solution of `ofGlobal E`. -/
def Solution.ofGlobal (E : ModuleDerived.{z} X) : Solution (ofGlobal E) where
  obj := E
  iso U := Iso.refl _
  iso_comp := sorry

/-- The global object of the tautological solution is the original object. -/
theorem Solution.ofGlobal_obj (E : ModuleDerived.{z} X) :
    (Solution.ofGlobal E).obj = E := sorry


end RingedSite.ModuleDerived
