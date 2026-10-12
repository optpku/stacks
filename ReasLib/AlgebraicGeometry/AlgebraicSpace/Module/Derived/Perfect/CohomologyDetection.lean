/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh

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
            ((DerivedCategory.cohomologyIn
              (SheafOfModules.isQuasicoherent (structureSheaf X))).ι.obj L))) →
          Subsingleton (K ⟶ (DerivedCategory.cohomologyIn
            (SheafOfModules.isQuasicoherent (structureSheaf X))).ι.obj L) := sorry

/-- Derived Ext from a perfect derived module on a quasi-compact absolutely quasi-separated
algebraic space to a bounded derived module with quasicoherent cohomology vanishes outside
a finite interval. -/
theorem exists_extSupportInterval_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {K : ModuleDerived X}
    (hK : ModuleDerived.IsPerfect K)
    (L : DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isQuasicoherent (structureSheaf X))) :
    ∃ c d : ℤ, c ≤ d ∧
      ∀ n : ℤ, n ∉ Set.Icc c d →
        Subsingleton (Ext⁽n⁾(K, DerivedCategory.Bounded.ι.obj L.obj)) := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh
