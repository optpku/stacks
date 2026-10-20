module

public import stacks_project.Chap82.Definition_82_18_1_ChernCap

/-!
# Commutativity of first-Chern cap on meromorphic-section divisors

In Situation 82.2.1, on a good integral algebraic space of `δ`-dimension `n`,
capping `c1(N)` against `div_L(s)` equals capping `c1(L)` against `div_N(t)`
in `CH_{n-2}(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- The meromorphic-section divisor cycle `div_L(s)` lies in
`cycleGroup f δ ((n - 2) + 1)` when `dim_δ(X) = n`. -/
theorem meromorphicSectionDivisorCycle_mem_sub_two_succ
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    meromorphicSectionDivisorCycle f δ s hs ∈ cycleGroup f δ ((n - 2) + 1) :=
  sorry

/-- Lemma 82.21.1: In Situation 82.2.1 let `X / B` be good. Assume `X` integral
and `dim_δ(X) = n`. Let `L`, `N` be invertible on `X`. Choose a nonzero
meromorphic section `s` of `L` and a nonzero meromorphic section `t` of `N`.
Set `α = div_L(s)` and `β = div_N(t)`. Then `c1(N) ∩ α = c1(L) ∩ β` in
`CH_{n-2}(X)`. -/
@[stacks 0EQX]
theorem firstChernClassCap_meromorphicSectionDivisor_comm
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t) :
    firstChernClassCap f δ N (n - 2)
        ⟨meromorphicSectionDivisorCycle f δ s hs,
          meromorphicSectionDivisorCycle_mem_sub_two_succ f δ n hX s hs⟩ =
      firstChernClassCap f δ L (n - 2)
        ⟨meromorphicSectionDivisorCycle f δ t ht,
          meromorphicSectionDivisorCycle_mem_sub_two_succ f δ n hX t ht⟩ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
