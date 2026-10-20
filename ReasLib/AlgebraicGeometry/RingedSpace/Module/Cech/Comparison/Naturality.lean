/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.FMap.Linear.Bundled
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of module Cech comparisons

For a morphism `f : X ⟶ Y`, both vertical arrows in the comparison square are canonical and
`Γ(Y, 𝒪_Y)`-linear.  The Cech map uses a bundled refinement of the inverse-image cover, while the
global-sections map restricts the `Γ(X, 𝒪_X)`-action along
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.  Thus the canonical ambient category is
`D⁺(ModuleCat (globalSectionsRing Y))`.

The horizontal arrows are coefficient-natural comparison choices asserted by Tag 01FD.  Their
normalization is recorded as a degree-zero invertibility certificate.  The naturality is part of
the datum itself; the certificate is deliberately weaker than a claim of uniqueness or of
invertibility in every degree.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech.Comparison

variable {X Y : RingedSpace.{u}}

/-- The coefficient-natural comparison type for a bundled cover of `Y`. -/
@[stacks 01FD "source coefficient-natural Cech comparison type"]
abbrev SourceComparison (𝒱 : OpenCover.{u} Y.carrier) : Type _ :=
  ModuleCech.Comparison (X := Y) (⊤ : Opens Y.carrier)
    (Opens.Cover.overFamily ⊤ 𝒱 𝒱.isCover.iSup_eq_top)

/-- The coefficient-natural comparison type for the target Cech functor, with scalars restricted
to `Γ(Y, 𝒪_Y)`. -/
@[stacks 01FD "target coefficient-natural Cech comparison type"]
abbrev TargetComparison (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) : Type _ :=
  FMap.Linear.Bundled.derivedTargetFunctor f 𝒰 ⟶
    (DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
      Module.Derived.GlobalSections.Bounded.restricted f)

namespace TargetComparison

/-- A target comparison is normalized when every coefficient component is invertible in degree
zero.  This is a certificate for reuse, rather than a uniqueness assertion. -/
@[stacks 01FD "degree-zero target comparison certificate"]
def IsNormalized {f : X ⟶ Y} {𝒰 : OpenCover.{u} X.carrier}
    (comparison : TargetComparison f 𝒰) : Prop :=
  ∀ F : X.Modules,
    IsIso ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat (globalSectionsRing Y)) 0).map (comparison.app F))

end TargetComparison

/-- A module-linear Cech-to-derived-sections square in
`D⁺(ModuleCat (globalSectionsRing Y))`.  Both horizontal comparison choices are normalized in
degree zero, and both vertical arrows are the canonical maps determined by the `f`-map and the
selected refinement. -/
@[stacks 01FD "module-linear derived Cech comparison square"]
structure FMapSquare
    (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) (𝒱 : OpenCover.{u} Y.carrier)
    (r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) where
  /-- The coefficient-natural comparison from the Cech source to derived global sections. -/
  source : SourceComparison 𝒱
  /-- The source comparison is invertible on degree-zero homology for every coefficient. -/
  sourceNormalized : ModuleCech.Comparison.IsNormalized (X := Y) (⊤ : Opens Y.carrier)
    (Opens.Cover.overFamily ⊤ 𝒱 𝒱.isCover.iSup_eq_top) source
  /-- The coefficient-natural target comparison after restriction of scalars to
  `Γ(Y, 𝒪_Y)`. -/
  target : TargetComparison f 𝒰
  /-- The target comparison is invertible on degree-zero homology for every coefficient. -/
  targetNormalized : TargetComparison.IsNormalized target
  /-- The two normalized comparisons intertwine the canonical Cech and derived-global-sections
  maps. -/
  comm : CommSq (CategoryTheory.NatTrans.app source G)
    (FMap.Linear.Bundled.derivedMap f 𝒰 𝒱 r φ)
    (Module.Derived.GlobalSections.Bounded.mapOfFMap f φ)
    (CategoryTheory.NatTrans.app target F)

namespace FMapSquare

/-- Lemma 20.15.1 (Tag 01FD): normalized module-linear comparisons can be chosen so that the
canonical change-of-space square commutes in `D⁺(ModuleCat (globalSectionsRing Y))`. -/
@[stacks 01FD "module-linear derived change-of-space Cech square"]
theorem nonempty
    (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) (𝒱 : OpenCover.{u} Y.carrier)
    (r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    Nonempty (FMapSquare f 𝒰 𝒱 r φ) := sorry

/-- Applying homology in any integral degree to a module-linear derived comparison square gives
a commutative square of `Γ(Y, 𝒪_Y)`-modules. -/
@[stacks 01FD "homology of the module-linear change-of-space Cech square"]
theorem homology_comm
    {f : X ⟶ Y} {𝒰 : OpenCover.{u} X.carrier} {𝒱 : OpenCover.{u} Y.carrier}
    {r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰}
    {G : Y.Modules} {F : X.Modules}
    {φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F}
    (square : FMapSquare f 𝒰 𝒱 r φ) (i : ℤ) :
    CommSq
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) i).map
        (CategoryTheory.NatTrans.app square.source G))
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) i).map
          (FMap.Linear.Bundled.derivedMap f 𝒰 𝒱 r φ))
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) i).map
          (Module.Derived.GlobalSections.Bounded.mapOfFMap f φ))
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) i).map
        (CategoryTheory.NatTrans.app square.target F)) := sorry

/-- The nonnegative-degree specialization of `homology_comm`, matching the ordinary Cech
cohomological grading in Lemma 20.15.1. -/
@[stacks 01FD "degreewise module-linear change-of-space Cech square"]
theorem degree_comm
    {f : X ⟶ Y} {𝒰 : OpenCover.{u} X.carrier} {𝒱 : OpenCover.{u} Y.carrier}
    {r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰}
    {G : Y.Modules} {F : X.Modules}
    {φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F}
    (square : FMapSquare f 𝒰 𝒱 r φ) (p : ℕ) :
    CommSq
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) (p : ℤ)).map
        (CategoryTheory.NatTrans.app square.source G))
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) (p : ℤ)).map
          (FMap.Linear.Bundled.derivedMap f 𝒰 𝒱 r φ))
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) (p : ℤ)).map
          (Module.Derived.GlobalSections.Bounded.mapOfFMap f φ))
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat (globalSectionsRing Y)) (p : ℤ)).map
        (CategoryTheory.NatTrans.app square.target F)) := sorry

end FMapSquare

end AlgebraicGeometry.RingedSpace.ModuleCech.Comparison
