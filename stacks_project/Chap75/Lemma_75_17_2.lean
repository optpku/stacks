module

public import stacks_project.Chap75.Lemma_75_17_2_CohomologyDetection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.17.2 (1): for a perfect object on a quasi-compact quasi-separated algebraic space,
there is a finite cohomological window whose vanishing detects vanishing of morphisms from
that object to any object of `D_QCoh(𝒪_X)`. -/
@[stacks 09MB] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.exists_homologyWindow_of_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {K : ModuleDerived X},
      ModuleDerived.IsPerfect K →
        ∃ a b : ℤ, a ≤ b ∧
          ∀ L : DerivedQCoh X,
            (∀ i ∈ Set.Icc a b,
              IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
                ((inclusion X).obj L))) →
              Subsingleton (K ⟶ (inclusion X).obj L))

/- Lemma 75.17.2 (2): derived Ext from a perfect object to a bounded object of
`D_QCoh(𝒪_X)` vanishes outside a finite interval of integer degrees. -/
@[stacks 09MB] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.exists_extSupportInterval_of_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {K : ModuleDerived X},
      ModuleDerived.IsPerfect K →
        ∀ L : DerivedCategory.Bounded.CohomologyIn (quasiCoherentModuleProperty X),
          ∃ c d : ℤ, c ≤ d ∧
            ∀ n : ℤ, n ∉ Set.Icc c d →
              Subsingleton (Ext⁽n⁾(K, DerivedCategory.Bounded.ι.obj L.obj)))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
