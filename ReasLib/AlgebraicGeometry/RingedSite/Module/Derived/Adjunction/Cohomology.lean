/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Flat
public import ReasLib.CategoryTheory.DerivedCategory.Adjunction.Cohomology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomological detection for flat derived pullback-pushforward adjunctions

The finite devissage theorem for arbitrary triangulated adjunctions is valid on two-sided bounded
objects. A flat pullback-pushforward adjunction has the additional t-structure compatibility
needed to detect its unit and counit on bounded-below objects. This module owns that
ringed-site-specific strengthening.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open DerivedCategory

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom.DerivedAdjunction

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable {f : X.Hom Y}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
variable [HasPair.{z} f]

/-- Lemma 21.28.3 (0D7S): for flat `f`, the derived counit is invertible on a bounded-below
object once it is invertible on the degree-zero single of every cohomology object. -/
@[stacks 0D7S "bounded-below detection of the flat derived counit"]
theorem counitIso_of_boundedBelow_of_homology [IsFlat.{z} f]
    (K : ModuleDerived.{z} X) (hbounded : IsBoundedBelow K)
    (hH : ∀ q : ℤ,
      (moduleDerivedAdjunction.{z} f).counitIsoProperty
        ((singleFunctor (ModuleCat.{z} X) (0 : ℤ)).obj
          ((homologyFunctor (ModuleCat.{z} X) q).obj K))) :
    (moduleDerivedAdjunction.{z} f).counitIsoProperty K := sorry

/-- Lemma 21.28.4 (0D7T): for flat `f`, the derived unit is invertible on a bounded-below
object once it is invertible on the degree-zero single of every cohomology object. -/
@[stacks 0D7T "bounded-below detection of the flat derived unit"]
theorem unitIso_of_boundedBelow_of_homology [IsFlat.{z} f]
    (K : ModuleDerived.{z} Y) (hbounded : IsBoundedBelow K)
    (hH : ∀ q : ℤ,
      (moduleDerivedAdjunction.{z} f).unitIsoProperty
        ((singleFunctor (ModuleCat.{z} Y) (0 : ℤ)).obj
          ((homologyFunctor (ModuleCat.{z} Y) q).obj K))) :
    (moduleDerivedAdjunction.{z} f).unitIsoProperty K := sorry

end RingedSite.Hom.DerivedAdjunction
