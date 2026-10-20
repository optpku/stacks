/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Ext

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a perfect derived module on a quasi-compact absolutely quasi-separated algebraic space,
there is a finite interval of cohomology degrees whose vanishing detects vanishing of morphisms
from that module to any derived module with quasicoherent cohomology. -/
theorem exists_homologyWindow_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {K : ModuleDerived X}
    (hK : ModuleDerived.IsPerfect K) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedQCoh X,
        (∀ i ∈ Set.Icc a b,
          IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
            ((DerivedQCoh.inclusion X).obj L))) →
          Subsingleton (K ⟶ (DerivedQCoh.inclusion X).obj L) := sorry

/-- Derived Ext from a perfect derived module on a quasi-compact absolutely quasi-separated
algebraic space to a bounded derived module with quasicoherent cohomology vanishes outside
a finite interval. -/
theorem exists_extSupportInterval_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {K : ModuleDerived X}
    (hK : ModuleDerived.IsPerfect K)
    (L : DerivedCategory.Bounded.CohomologyIn (quasiCoherentModuleProperty X)) :
    ∃ c d : ℤ, c ≤ d ∧
      ∀ n : ℤ, n ∉ Set.Icc c d →
        Subsingleton (Ext⁽n⁾(K, DerivedCategory.Bounded.ι.obj L.obj)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
