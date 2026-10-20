/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow.Single
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below derived global sections of a direct image

The common target for change of space is `D⁺(Γ(Y, 𝒪_Y))`: derived global sections on
`X` are followed by restriction of scalars along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.  This
retains module linearity and makes the variance in the textbook map explicit.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded

variable {X Y : RingedSpace.{u}}

/-- The bounded-below total right-derived global-sections functor. -/
abbrev functor (X : RingedSpace.{u}) :=
  Functor.RightDerived.Bounded.functor (moduleGlobalSectionsFunctor X)

/-- The bounded-below right-derived restriction of scalars on global-section modules. -/
abbrev restriction (f : X ⟶ Y) :=
  Functor.RightDerived.Bounded.functor (moduleSectionsRestrictionFunctor f ⊤)

/-- Bounded-below derived sections on `X`, restricted to modules over `Γ(Y, 𝒪_Y)`. -/
abbrev restricted (f : X ⟶ Y) :=
  Module.Derived.Sections.Pushforward.source f ⊤

/-- Bounded-below derived pushforward followed by derived global sections on `Y`. -/
abbrev afterPushforward (f : X ⟶ Y) :=
  Module.Derived.Sections.Pushforward.target f ⊤

/-- Restricted bounded-below derived global sections on `X` are canonically isomorphic to
bounded-below derived global sections on `Y` after `Rf_*`. -/
@[stacks 01F9 "bounded-below derived global sections and direct image"]
noncomputable def pushforwardIso (f : X ⟶ Y) :
    restricted f ≅ afterPushforward f :=
  Module.Derived.Sections.Pushforward.iso f ⊤

/-- A morphism `L ⟶ Rf_* K` in `D⁺` induces the change-of-space map on bounded-below
derived global sections, with the target scalars restricted to `Γ(Y, 𝒪_Y)`. -/
@[stacks 01F9 "bounded derived global-sections map from a direct-image morphism"]
noncomputable def mapOfPushforward (f : X ⟶ Y)
    {K : DerivedCategory.Plus X.Modules} {L : DerivedCategory.Plus Y.Modules}
    (α : L ⟶ (moduleDerivedPushforwardPlus f).obj K) :
    (functor Y).obj L ⟶ (restricted f).obj K :=
  (functor Y).map α ≫ (pushforwardIso f).inv.app K

/-- An `f`-map `G ⟶ f_* F` induces the canonical map in
`D⁺(Γ(Y, 𝒪_Y))` from derived global sections of `G` to restricted derived global
sections of `F`. -/
@[stacks 01F9 "bounded derived global-sections map of an f-map"]
noncomputable def mapOfFMap (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    (functor Y).obj ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj G) ⟶
      (restricted f).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) :=
  mapOfPushforward f (moduleDerivedPushforwardPlus.comparison f φ)

/-- The bounded `f`-map entry point is the specialization of `mapOfPushforward` along the
canonical bounded direct-image comparison. -/
@[stacks 01F9 "coherence of bounded derived global-sections f-maps"]
theorem mapOfFMap_eq_mapOfPushforward
    (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    mapOfFMap f φ =
      mapOfPushforward f (moduleDerivedPushforwardPlus.comparison f φ) := sorry

/-- The bounded change-of-space construction is natural in a square of morphisms into derived
pushforward. -/
@[stacks 01F9 "naturality of bounded derived global-sections change of space"]
theorem mapOfPushforward_natural (f : X ⟶ Y)
    {K K' : DerivedCategory.Plus X.Modules} {L L' : DerivedCategory.Plus Y.Modules}
    (α : L ⟶ (moduleDerivedPushforwardPlus f).obj K)
    (α' : L' ⟶ (moduleDerivedPushforwardPlus f).obj K')
    (a : L ⟶ L') (b : K ⟶ K')
    (h : α ≫ (moduleDerivedPushforwardPlus f).map b = a ≫ α') :
    (functor Y).map a ≫ mapOfPushforward f α' =
      mapOfPushforward f α ≫ (restricted f).map b := sorry

/-- The bounded change-of-space map is natural in commutative squares of `f`-maps. -/
@[stacks 01F9 "naturality of bounded derived global-sections f-maps"]
theorem mapOfFMap_natural (f : X ⟶ Y)
    {G G' : Y.Modules} {F F' : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F)
    (φ' : G' ⟶ (RingedSpace.Hom.pushforward f).obj F')
    (a : G ⟶ G') (b : F ⟶ F')
    (h : φ ≫ (RingedSpace.Hom.pushforward f).map b = a ≫ φ') :
    (functor Y).map ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map a) ≫
        mapOfFMap f φ' =
      mapOfFMap f φ ≫
        (restricted f).map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map b) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded
