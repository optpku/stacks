/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.SectionsComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived global sections of a direct image

This file owns the change-of-space map on unbounded derived global sections induced by a morphism
into a direct image.  The bounded-below, cohomology, and underlying-additive interfaces live in
the corresponding `Pushforward.*` leaves.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections

variable {X Y : RingedSpace.{u}}

/-- Derived global sections on `X`, after restriction along
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`, are canonically isomorphic to derived global sections on
`Y` after `Rf_*`. -/
@[stacks 01F9 "derived global sections and direct image",
  stacks 01FD "derived global sections and direct image"]
noncomputable def pushforwardIso (f : X ⟶ Y) :
    functor X ⋙ moduleSectionsRestrictionDerived f ⊤ ≅
      moduleDerivedPushforward f ⋙ functor Y :=
  RingedSite.Hom.ModuleSections.objectPushforwardComparisonIso
    (opensRingedSiteHom f) (⊤ : Opens Y.carrier)

/-- A morphism `L ⟶ Rf_* K` induces the change-of-space map
`RΓ(Y, L) ⟶ RΓ(X, K)`, with scalars restricted along the global-sections map. -/
@[stacks 01F9 "derived global-sections map from a direct-image morphism",
  stacks 01FD "derived global-sections map from a direct-image morphism"]
noncomputable def mapOfPushforward (f : X ⟶ Y)
    {K : DerivedCategory X.Modules} {L : DerivedCategory Y.Modules}
    (α : L ⟶ (moduleDerivedPushforward f).obj K) :
    (functor Y).obj L ⟶
      (moduleSectionsRestrictionDerived f ⊤).obj ((functor X).obj K) :=
  (functor Y).map α ≫ (pushforwardIso f).inv.app K

/-- The derived global-sections map induced by an `f`-map `φ : G ⟶ f_* F`, using the
canonical single-complex comparison. -/
@[stacks 01F9 "derived global-sections map of an f-map",
  stacks 01FD "derived global-sections map of an f-map"]
noncomputable def mapOfFMap (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    (functor Y).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ⟶
      (moduleSectionsRestrictionDerived f ⊤).obj
        ((functor X).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :=
  moduleDerivedPushforward.globalSectionsMap f G F φ ≫
    (pushforwardIso f).inv.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)

/-- The `f`-map entry point is the specialization of `mapOfPushforward` along the canonical
single-complex direct-image comparison. -/
@[stacks 01F9 "coherence of derived global-sections f-maps",
  stacks 01FD "coherence of derived global-sections f-maps"]
theorem mapOfFMap_eq_mapOfPushforward
    (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    mapOfFMap f φ =
      mapOfPushforward f (moduleDerivedPushforward.comparison f G F φ) := sorry

/-- The change-of-space construction is natural in a morphism into derived direct image. -/
@[stacks 01F9 "naturality of derived global-sections change of space",
  stacks 01FD "naturality of derived global-sections change of space"]
theorem mapOfPushforward_natural (f : X ⟶ Y)
    {K K' : DerivedCategory X.Modules} {L L' : DerivedCategory Y.Modules}
    (α : L ⟶ (moduleDerivedPushforward f).obj K)
    (α' : L' ⟶ (moduleDerivedPushforward f).obj K')
    (a : L ⟶ L') (b : K ⟶ K')
    (h : α ≫ (moduleDerivedPushforward f).map b = a ≫ α') :
    (functor Y).map a ≫ mapOfPushforward f α' =
      mapOfPushforward f α ≫
        (moduleSectionsRestrictionDerived f ⊤).map ((functor X).map b) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
