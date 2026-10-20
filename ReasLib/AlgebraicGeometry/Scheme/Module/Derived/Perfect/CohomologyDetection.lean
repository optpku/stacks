/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Ext

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a perfect derived module on a quasi-compact quasi-separated scheme, there is a
finite interval of cohomology degrees whose vanishing detects vanishing of morphisms from
that module to any derived module with quasicoherent cohomology. -/
theorem exists_homologyWindow_of_isPerfect {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {K : RingedSpace.ModuleDerived X.toRingedSpace}
    (hK : RingedSpace.ModuleDerived.IsPerfect K) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedCategory.CohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace),
        (∀ i ∈ Set.Icc a b,
          IsZero ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules i).obj
            ((DerivedCategory.cohomologyIn
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι.obj L))) →
          Subsingleton
            (K ⟶ (DerivedCategory.cohomologyIn
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι.obj L) := sorry

/-- Derived Ext from a perfect derived module on a quasi-compact quasi-separated scheme to a
bounded derived module with quasicoherent cohomology vanishes outside a finite interval. -/
theorem exists_extSupportInterval_of_isPerfect {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {K : RingedSpace.ModuleDerived X.toRingedSpace}
    (hK : RingedSpace.ModuleDerived.IsPerfect K)
    (L : DerivedCategory.Bounded.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    ∃ c d : ℤ, c ≤ d ∧
      ∀ n : ℤ, n ∉ Set.Icc c d →
        Subsingleton (Ext⁽n⁾(K, DerivedCategory.Bounded.ι.obj L.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
