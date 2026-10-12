/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Lemma_82_15_2_Localization

/-!
# Exactness of the open-closed localization sequence of Chow groups

In the good setup of Situation 82.2.1, if two cycles become rationally
equivalent after restriction to an open subspace, their difference is
rationally equivalent to a cycle pushed forward from the reduced closed
complement. Equivalently the induced sequence of Chow groups is exact and
surjective onto `CH_k(U)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom
namespace ChowLocalization

/-- Lemma 82.15.2 (1): In Situation 82.2.1 let `X / B` be good. Let `U ⊂ X` be an
open subspace. Let `Y` be the reduced closed subspace of `X` with
`|Y| = |X| \ |U|` and denote `i : Y ⟶ X` the inclusion morphism. Let `k ∈ ℤ`.
If `α, β ∈ Z_k(X)` satisfy `α|_U ∼_rat β|_U`, then there exists a cycle
`γ ∈ Z_k(Y)` such that `α ∼_rat β + i_* γ`. Here `Y` is `U.reducedComplement`,
`i` is `Y.ι`, restriction to `U` is `Localization.openPullback`, and `i_*` is
`Localization.closedPushforward`. -/
@[stacks 0EQ7]
theorem exists_closedPushforward {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (U : OpenSubspace X) (k : ℤ) (α β : (Hom.cycleGroup (f)) δ k)
    (h : RationalEquivalence.RationallyEquivalent (U.ι ≫ f) δ k
      (Localization.openPullback f δ U k α)
      (Localization.openPullback f δ U k β)) :
    ∃ γ : (Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k,
      RationalEquivalence.RationallyEquivalent f δ k α
        (β + Localization.closedPushforward f δ U k γ) :=
  sorry

/-- Lemma 82.15.2 (2): In Situation 82.2.1 let `X / B` be good. Let `U ⊂ X` be an
open subspace. Let `Y` be the reduced closed subspace of `X` with
`|Y| = |X| \ |U|` and denote `i : Y ⟶ X` the inclusion morphism. For every
`k ∈ ℤ` the sequence `CH_k(Y) ⟶ CH_k(X) ⟶ CH_k(U) ⟶ 0` given by `i_*` then
`j^*` is an exact complex of abelian groups. Here `Y` is `U.reducedComplement`,
`i` is `Y.ι`, `j` is `U.ι`, and `CH_k` is `chowGroup` of the structure morphism
to `B`. -/
@[stacks 0EQ7]
theorem exact {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (U : OpenSubspace X) (k : ℤ) :
    (complex f δ U k).Exact ∧ Epi (complex f δ U k).g :=
  sorry

end ChowLocalization
end AlgebraicGeometry.AlgebraicSpace.Hom
