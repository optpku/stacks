module

public import stacks_project.Chap75.Lemma_75_26_4_Locus
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 75.26.4: for a scheme `S`, an algebraic space `X` over `S`, and a perfect object
`E` of `D(𝒪_X)`, each pair `i, r : ℤ` with `0 ≤ r` determines a canonical open subspace
`U ⊂ X` on which `E|_U ≅ H^i(E|_U)[-i]` with `H^i(E|_U)` locally free of rank `r`, and a
morphism `f : Y ⟶ X` factors through `U` if and only if `Lf^* E` is a locally free module
of rank `r` placed in degree `i`. For `r < 0` the locus is empty and the rank-`r` property
is unsatisfiable. -/
@[stacks 0D20]
theorem IsPerfect.vectorBundleLocus_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {E : ModuleDerived X} (hE : IsPerfect E) (i r : ℤ) (hr : 0 ≤ r) :
    IsVectorBundleOfRankInDegree
        ((pullback (IsPerfect.vectorBundleLocus hE i r).ι).obj E) i r ∧
      ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
        (∃ g : Y ⟶ (IsPerfect.vectorBundleLocus hE i r).X,
            g ≫ (IsPerfect.vectorBundleLocus hE i r).ι = f) ↔
          IsVectorBundleOfRankInDegree ((modulePullbackDerived f).obj E) i r :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
