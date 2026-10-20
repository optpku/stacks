/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived.Category
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

/-!
# Restriction of derived module sheaves to slices
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z u v w

namespace SheafOfModules.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J RingCat.{w})

/-- Restriction of module sheaves along a morphism between slice bases. -/
abbrev restriction {U V : C} (f : V ⟶ U) :
    SheafOfModules.{z} (O.over U) ⥤ SheafOfModules.{z} (O.over V) :=
  SheafOfModules.overMap O f

/-- Slice restriction is additive. -/
instance restriction_additive {U V : C} (f : V ⟶ U) :
    (restriction.{z} O f).Additive := by
  dsimp only [restriction, SheafOfModules.overMap]
  infer_instance

/-- Slice restriction preserves finite limits. -/
instance restriction_preservesFiniteLimits {U V : C} (f : V ⟶ U) :
    PreservesFiniteLimits (restriction.{z} O f) := sorry

/-- Slice restriction preserves finite colimits. -/
instance restriction_preservesFiniteColimits {U V : C} (f : V ⟶ U) :
    PreservesFiniteColimits (restriction.{z} O f) := sorry

/-- The composite of the slice functors associated to two arrows is continuous. -/
instance overMap_comp_isContinuous {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (Over.map g ⋙ Over.map f).IsContinuous (J.over W) (J.over U) :=
  Functor.isContinuous_comp (Over.map g) (Over.map f) (J.over W) (J.over V) (J.over U)

/-- The ring-sheaf morphism inducing slice restriction is the inverse canonical comparison. -/
abbrev restrictionRingHom {U V : C} (f : V ⟶ U) :
    O.over V ⟶ ((Over.map f).sheafPushforwardContinuous RingCat.{w}
      (J.over V) (J.over U)).obj (O.over U) :=
  (Sheaf.pushforwardOverMapIso O f).inv

/-- Sequential slice restrictions identify with pushforward along the composite slice functor. -/
def restrictionCompPushforward {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restriction.{z} O f ⋙ restriction O g ≅
      SheafOfModules.pushforward (F := Over.map g ⋙ Over.map f)
        (restrictionRingHom O g ≫
          ((Over.map g).sheafPushforwardContinuous RingCat.{w}
            (J.over W) (J.over V)).map (restrictionRingHom O f)) :=
  SheafOfModules.pushforwardComp (restrictionRingHom O g) (restrictionRingHom O f)

/-- The ring-sheaf maps for direct and sequential slice restriction agree under composition. -/
theorem restriction_comp_ringHom {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionRingHom O (g ≫ f) ≫
        (Functor.sheafPushforwardContinuousNatTrans (Over.mapComp g f).symm.hom
          RingCat.{w} (J.over W) (J.over U)).app (O.over U) =
      restrictionRingHom O g ≫
        ((Over.map g).sheafPushforwardContinuous RingCat.{w}
          (J.over W) (J.over V)).map (restrictionRingHom O f) := sorry

/-- Direct slice restriction identifies canonically with sequential slice restriction. -/
def restrictionComp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restriction.{z} O (g ≫ f) ≅ restriction O f ⋙ restriction O g :=
  SheafOfModules.pushforwardCongr₂ (restrictionRingHom O (g ≫ f)) (Over.mapComp g f).symm
      (restriction_comp_ringHom O f g) ≪≫ (restrictionCompPushforward O f g).symm

/-- Slice restriction as a bundled exact functor. -/
abbrev restrictionExact {U V : C} (f : V ⟶ U) :
    SheafOfModules.{z} (O.over U) ⥤ₑ SheafOfModules.{z} (O.over V) :=
  ExactFunctor.of (restriction O f)

/-- The canonical slice composition comparison is an isomorphism of exact functors. -/
def restrictionCompExactIso {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionExact.{z} O (g ≫ f) ≅ (restrictionExact O f).comp (restrictionExact O g) :=
  ObjectProperty.isoMk (exactFunctor _ _) (restrictionComp O f g)

/-- Ambient restriction to a slice as a bundled exact functor.  The underlying functor is the
canonical slice restriction `SheafOfModules.Localization.restriction`, whose exactness instances
live with that owner. -/
abbrev localizedRestrictionExact (U : C) :
    SheafOfModules.{z} O ⥤ₑ SheafOfModules.{z} (O.over U) :=
  ExactFunctor.of (Localization.restriction O U)

/-- Restriction first to a slice and then along a slice arrow equals direct restriction. -/
def restrictionIteratedIso {U V : C} (f : V ⟶ U) :
    (Localization.restriction O U : SheafOfModules.{z} O ⥤ _) ⋙ restriction O f ≅
      Localization.restriction O V :=
  SheafOfModules.overFunctorMap O f

/-- The iterated ambient restriction comparison is an isomorphism of exact functors. -/
def restrictionIteratedExactIso {U V : C} (f : V ⟶ U) :
    (localizedRestrictionExact.{z} O U).comp (restrictionExact O f) ≅
      localizedRestrictionExact O V :=
  ObjectProperty.isoMk (exactFunctor _ _) (restrictionIteratedIso O f)

variable [abelianOver : ∀ U : C, Abelian (SheafOfModules.{z} (O.over U))]

/-- The derived functor of slice restriction, using standard derived categories. -/
def restrictionDerived {U V : C} (f : V ⟶ U) :
    Derived.{z} (O.over U) ⥤ Derived.{z} (O.over V) :=
  (restrictionExact O f).mapDerivedCategory

/-- Equal slice arrows induce canonically identified derived restriction functors. -/
def restrictionDerivedCongr {U V : C} {f g : V ⟶ U} (h : f = g) :
    restrictionDerived O f ≅ restrictionDerived O g :=
  eqToIso (congrArg (restrictionDerived O) h)

/-- Derived direct restriction identifies canonically with derived sequential restriction. -/
def restrictionCompIso {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restrictionDerived O (g ≫ f) ≅ restrictionDerived O f ⋙ restrictionDerived O g :=
  ExactFunctor.MapDerivedCategory.mapIso (restrictionCompExactIso O f g) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso (restrictionExact O f) (restrictionExact O g)

variable [abelian : Abelian (SheafOfModules.{z} O)]

/-- The derived functor of restriction from the ambient site to a slice. -/
abbrev localizedRestrictionDerived (U : C) :
    Derived.{z} O ⥤ Derived.{z} (O.over U) :=
  (localizedRestrictionExact O U).mapDerivedCategory

/-- Derived iterated ambient restriction identifies canonically with direct restriction. -/
def restrictionDerivedIteratedIso {U V : C} (f : V ⟶ U) :
    localizedRestrictionDerived O U ⋙ restrictionDerived O f ≅ localizedRestrictionDerived O V :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
    (localizedRestrictionExact O U) (restrictionExact O f)).symm ≪≫
      ExactFunctor.MapDerivedCategory.mapIso (restrictionIteratedExactIso O f)

end SheafOfModules.Derived
