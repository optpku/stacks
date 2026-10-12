/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived pushforward of modules on ringed spaces

This module owns the cochain-level and unbounded derived direct-image functors for morphisms of
ringed spaces, together with their canonical comparison maps.  The independent `RΓ` API lives in
`Derived.GlobalSections`.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The cochain-level pushforward functor followed by localization to the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pushforward f).Additive] :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory Y.Modules :=
  Functor.RightDerived.Cochain.toDerived (pushforward f)

namespace opensRingedSiteHom.DerivedPushforward

/-- Direct image along an opens-ringed-site morphism has the canonical total right derived
functor supplied by the Grothendieck-abelian module category. -/
instance hasDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Functor.HasRightDerivedFunctor
      (_root_.RingedSite.Hom.modulePushforwardToDerived.{u} (opensRingedSiteHom f))
      (_root_.RingedSite.Hom.ModuleQis.{u} X.opensRingedSite) := by
  exact _root_.RingedSite.Hom.modulePushforwardToDerived.hasRightDerived.{u}
    (opensRingedSiteHom f)

namespace Composition

/-- Direct image along a composite of opens-ringed-site morphisms has the same canonical total
right derived functor. -/
instance hasDerived {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.HasRightDerivedFunctor
      (_root_.RingedSite.Hom.modulePushforwardToDerived.{u}
        (opensRingedSiteHom f ≫ opensRingedSiteHom g))
      (_root_.RingedSite.Hom.ModuleQis.{u} X.opensRingedSite) := by
  exact _root_.RingedSite.Hom.modulePushforwardToDerived.hasRightDerived.{u}
    (opensRingedSiteHom f ≫ opensRingedSiteHom g)

end Composition
end opensRingedSiteHom.DerivedPushforward

/-- The total right derived pushforward functor on derived categories of `𝒪_X`-modules. -/
@[stacks 05S9 "total right-derived pushforward"]
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pushforward f).Additive] :
    DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  Functor.RightDerived.Homotopy.functor (pushforward f)

namespace moduleDerivedPushforward

/-- Degree-`n` cohomology after total right-derived pushforward. -/
@[stacks 05S9 "cohomology after total right-derived pushforward"]
abbrev cohomologyFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pushforward f).Additive] (n : ℤ) :
    DerivedCategory X.Modules ⥤ Y.Modules :=
  Functor.RightDerived.Homotopy.cohomologyFunctor (pushforward f) n

/-- Degree-`n` cohomology after localizing a cochain complex and applying total right-derived
pushforward. -/
@[stacks 05S9 "cochain-level total right-derived pushforward cohomology"]
abbrev cochainCohomologyFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pushforward f).Additive] (n : ℤ) :
    CochainComplex X.Modules ℤ ⥤ Y.Modules :=
  Functor.RightDerived.Homotopy.cochainCohomologyFunctor (pushforward f) n

/-- The degree-`n` cohomology of the derived pushforward of a cochain complex. -/
@[stacks 05S9 "derived pushforward cohomology"]
abbrev cochainCohomology
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pushforward f).Additive]
    (K : CochainComplex X.Modules ℤ) (n : ℤ) : Y.Modules :=
  Functor.RightDerived.Homotopy.cochainCohomology (pushforward f) K n

/-- The map on derived pushforward cohomology induced by a cochain map. -/
@[stacks 05S9 "map on derived pushforward cohomology"]
abbrev cochainCohomologyMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pushforward f).Additive]
    {K L : CochainComplex X.Modules ℤ} (g : K ⟶ L) (n : ℤ) :
    cochainCohomology f K n ⟶ cochainCohomology f L n :=
  Functor.RightDerived.Homotopy.cochainCohomologyMap (pushforward f) g n

/-- The canonical unit from cochain-level pushforward followed by localization to the derived
pushforward functor `R(f)_*`. -/
noncomputable abbrev unit
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pushforward f).Additive] :
    modulePushforwardToDerived f ⟶
      (DerivedCategory.Q :
        CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
          moduleDerivedPushforward f :=
  Functor.RightDerived.Homotopy.cochainUnit (pushforward f)

/-- The canonical morphism `𝒢[0] ⟶ Rf_*(ℱ[0])` induced by a morphism
`φ : 𝒢 ⟶ f_* ℱ`. -/
noncomputable abbrev comparison
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (𝒢 : Y.Modules) (ℱ : X.Modules)
    (φ : 𝒢 ⟶ (pushforward f).obj ℱ) :
    (DerivedCategory.singleFunctor Y.Modules 0).obj 𝒢 ⟶
      (moduleDerivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ) :=
  (DerivedCategory.Q.map ((CochainComplex.singleFunctor Y.Modules 0).map φ)) ≫
    DerivedCategory.Q.map (((pushforward f).mapCochainComplexSingleFunctor 0).inv.app ℱ) ≫
    (unit f).app
      ((CochainComplex.singleFunctor X.Modules 0).obj ℱ)

/-- Applying derived global sections to the canonical single-complex comparison. -/
noncomputable abbrev globalSectionsMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (𝒢 : Y.Modules) (ℱ : X.Modules)
    (φ : 𝒢 ⟶ (pushforward f).obj ℱ) :
    (Module.Derived.GlobalSections.functor Y).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj 𝒢) ⟶
      (Module.Derived.GlobalSections.functor Y).obj
        ((moduleDerivedPushforward f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) :=
  (Module.Derived.GlobalSections.functor Y).map
    (comparison f 𝒢 ℱ φ)

end moduleDerivedPushforward

end AlgebraicGeometry.RingedSpace
namespace RingedSpaceDerivedPushforward

scoped notation:max "R(" f ")_*" =>
  AlgebraicGeometry.RingedSpace.moduleDerivedPushforward f

end RingedSpaceDerivedPushforward
