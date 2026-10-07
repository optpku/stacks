module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

/-!
# Homology windows for perfect objects on algebraic spaces

On a quasi-compact quasi-separated algebraic space, morphisms out of a perfect object of
`D(𝒪_X)` into objects of `D_QCoh(𝒪_X)` are detected by vanishing of cohomology on a finite
interval depending only on the perfect object, and derived Ext into a bounded such object
has finite support.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a perfect derived module on a quasi-compact quasi-separated algebraic space, there is a
finite interval of cohomology degrees whose vanishing detects vanishing of morphisms from
that module to any derived module with quasicoherent cohomology. -/
theorem exists_homologyWindow_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {K : ModuleDerived X}
    (hK : ModuleDerived.IsPerfect K) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedQCoh X,
        (∀ i ∈ Set.Icc a b,
          IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
            ((inclusion X).obj L))) →
          Subsingleton (K ⟶ (inclusion X).obj L) := sorry

/-- Derived Ext from a perfect derived module on a quasi-compact quasi-separated algebraic space
to a bounded derived module with quasicoherent cohomology vanishes outside a finite interval. -/
theorem exists_extSupportInterval_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {K : ModuleDerived X}
    (hK : ModuleDerived.IsPerfect K)
    (L : DerivedCategory.Bounded.CohomologyIn (quasiCoherentModuleProperty X)) :
    ∃ c d : ℤ, c ≤ d ∧
      ∀ n : ℤ, n ∉ Set.Icc c d →
        Subsingleton (Ext⁽n⁾(K, DerivedCategory.Bounded.ι.obj L.obj)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
