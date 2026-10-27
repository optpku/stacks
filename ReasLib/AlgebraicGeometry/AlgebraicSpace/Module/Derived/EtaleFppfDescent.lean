/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.EtaleFppfComparison

/-!
# Canonical unbounded derived units along `ε_X` and `a_X`

An object `K` of `D_QCoh(𝒪_X)`, after the objectwise carrier lift to
`ModuleCat.{u + 1}`, has canonical maps
`Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` and `K ⟶ Ra_{X,*}(La_X^* K)` in the
unbounded derived category of modules. The first is the derived `ε_X`-unit
at `Lπ_X^* K`, composed with `Rε_{X,*}` of the derived-pullback comparison
for `a_X = π_X ∘ ε_X`; the second is the derived `a_X`-unit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite
open RingedSite.Hom
open scoped RingedSiteDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

variable {S : Scheme.{u}}

/-- Derived objectwise carrier lift from `D(𝒪_X)` to modules of universe `u + 1`
on the small étale ringed site. -/
abbrev moduleCarrierLiftDerived (X : AlgebraicSpace S) :
    AlgebraicGeometry.AlgebraicSpace.ModuleDerived X ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X) :=
  @Functor.mapDerivedCategory
    (Modules X) inferInstance inferInstance (modulesHasDerivedCategory X)
    (ModuleCat.{u + 1} (ringedSite X)) inferInstance inferInstance
    (moduleCat_hasDerivedCategory.{u + 1} (ringedSite X))
    (RingedSite.Module.carrierLiftFunctor (ringedSite X))
    (RingedSite.Module.carrierLiftFunctor_additive (ringedSite X))
    (RingedSite.Module.carrierLiftFunctor_preservesFiniteLimits (ringedSite X))
    (RingedSite.Module.carrierLiftFunctor_preservesFiniteColimits (ringedSite X))

/-- Total left-derived pullback along `π_X` exists at universe `u + 1`. -/
instance etalePi_modulePullbackDerived_hasLeftDerived (X : AlgebraicSpace S) :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (Etale.Atlas.etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X)) := sorry

/-- Total left-derived pullback along `ε_X` exists at universe `u + 1`. -/
instance epsilon_modulePullbackDerived_hasLeftDerived (X : AlgebraicSpace S) :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (Etale.Atlas.overEtaleRingedSite X)) := sorry

/-- Total left-derived pullback along `a_X` exists at universe `u + 1`. -/
instance a_modulePullbackDerived_hasLeftDerived (X : AlgebraicSpace S) :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X)) := sorry

/-- The derived pullback-pushforward pair condition for `ε_X`. -/
instance epsilon_moduleDerivedAdjunction_hasPair (X : AlgebraicSpace S) :
    DerivedAdjunction.HasPair.{u + 1} (epsilonRingedHom X) := sorry

/-- The derived pullback-pushforward pair condition for `a_X`. -/
instance a_moduleDerivedAdjunction_hasPair (X : AlgebraicSpace S) :
    DerivedAdjunction.HasPair.{u + 1} (aRingedHom X) := sorry

/-- The canonical map `Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` after the carrier lift. -/
def piPullbackDerivedUnit {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X)) :
    (modulePullbackDerived.{u + 1} (Etale.Atlas.etalePiRingedHom X)).obj K ⟶
      (modulePushforwardDerived.{u + 1} (epsilonRingedHom X)).obj
        ((modulePullbackDerived.{u + 1} (aRingedHom X)).obj K) :=
  (moduleDerivedAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
      ((modulePullbackDerived.{u + 1} (Etale.Atlas.etalePiRingedHom X)).obj K) ≫
    (modulePushforwardDerived.{u + 1} (epsilonRingedHom X)).map
      ((@modulePullbackDerived.compComparison.{u + 1} _ _ _
          (epsilonRingedHom X) (Etale.Atlas.etalePiRingedHom X)
          inferInstance inferInstance inferInstance
          inferInstance inferInstance
          inferInstance inferInstance (a_modulePullbackDerived_hasLeftDerived X)).app K)

/-- `piPullbackDerivedUnit` is the derived `ε_X`-unit at `Lπ_X^* K`, followed by
`Rε_{X,*}` of the derived-pullback comparison for `a_X = π_X ∘ ε_X`. -/
theorem piPullbackDerivedUnit_eq {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X)) :
    piPullbackDerivedUnit K =
      (moduleDerivedAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
          ((modulePullbackDerived.{u + 1} (Etale.Atlas.etalePiRingedHom X)).obj K) ≫
        (modulePushforwardDerived.{u + 1} (epsilonRingedHom X)).map
          ((@modulePullbackDerived.compComparison.{u + 1} _ _ _
              (epsilonRingedHom X) (Etale.Atlas.etalePiRingedHom X)
              inferInstance inferInstance inferInstance
              inferInstance inferInstance
              inferInstance inferInstance (a_modulePullbackDerived_hasLeftDerived X)).app K) := sorry

/-- The canonical map `K ⟶ Ra_{X,*}(La_X^* K)` after the carrier lift. -/
def aDerivedUnit {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X)) :
    K ⟶
      (modulePushforwardDerived.{u + 1} (aRingedHom X)).obj
        ((modulePullbackDerived.{u + 1} (aRingedHom X)).obj K) :=
  (moduleDerivedAdjunction.{u + 1} (aRingedHom X)).unit.app K

/-- `aDerivedUnit` is the derived `a_X`-adjunction unit. -/
theorem aDerivedUnit_eq {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X)) :
    aDerivedUnit K =
      (moduleDerivedAdjunction.{u + 1} (aRingedHom X)).unit.app K := sorry

/-- For `K` in `D_QCoh(𝒪_X)`, the map `Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` is an
isomorphism. -/
instance piPullbackDerivedUnit_isIso {X : AlgebraicSpace S} (K : DerivedQCoh X) :
    IsIso (piPullbackDerivedUnit ((moduleCarrierLiftDerived X).obj K.obj)) := sorry

/-- For `K` in `D_QCoh(𝒪_X)`, the map `K ⟶ Ra_{X,*}(La_X^* K)` is an
isomorphism. -/
instance aDerivedUnit_isIso {X : AlgebraicSpace S} (K : DerivedQCoh X) :
    IsIso (aDerivedUnit ((moduleCarrierLiftDerived X).obj K.obj)) := sorry

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
