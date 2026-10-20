/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.LowerShriek

/-! # Étale lower shriek of modules and its derived functor -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.lowerShriek :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    U.Modules ⥤ X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.lowerShriekAdjunction :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    lowerShriek f ⊣ restrictFunctor f)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.lowerShriekDerived :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules] [(lowerShriek f).Additive]
    [PreservesFiniteLimits (lowerShriek f)] [PreservesFiniteColimits (lowerShriek f)],
    ModuleDerived U ⥤ ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.lowerShriekDerived_eq :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules] [(lowerShriek f).Additive]
    [PreservesFiniteLimits (lowerShriek f)] [PreservesFiniteColimits (lowerShriek f)],
    lowerShriekDerived f =
      @Functor.mapDerivedCategory U.Modules _ U.modulesAbelian (modulesHasDerivedCategory U)
        X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (lowerShriek f)
        inferInstance inferInstance inferInstance)
