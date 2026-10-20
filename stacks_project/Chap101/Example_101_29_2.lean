/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap101.Example_101_29_2_Action
public import stacks_project.Chap101.Example_101_29_2_Stratum
import StacksCheckRecall

/-!
# Example 101.29.2

The weighted `𝔾ₘ`-action on infinite affine space over a field yields an algebraic stack
`[U / 𝔾ₘ]` with an infinite stratification by reduced locally closed gerbes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
open FiberedCategoryOver.Groupoids.Hom
open scoped AlgebraicGeometry Bicategory

universe u

/- Example 101.29.2 (1): for a field `k` and a prime `p`, the quotient stack
`𝒳 = [U / 𝔾ₘ]` of the weighted action `t · x_i = t^(p^i) x_i` on
`U = Spec(k[x_i | i : ℕ])` is an algebraic stack. -/
@[stacks 06RE]
#check WeightedInfiniteAffine.instAlgebraicStack

/-- Example 101.29.2 (2): the strata `𝒳_i` and `𝒳_∞` are reduced locally closed
substacks of `𝒳`, with `𝒳_i` the quotient of the locus on `U` where `x_0, …, x_{i-1}`
vanish and `x_i` is a unit, and with `𝒳_∞` the quotient of the locus where every
`x_j` vanishes. -/
@[stacks 06RE]
theorem stratum_spec (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    (stratum k p hp i).Y = stratumStack k p hp i ∧
      (stratum k p hp i).ι = stratumι k p hp i ∧
      AlgebraicGeometry.IsReduced (locus k i).left ∧
      (match i with
        | StratumIndex.ofNat n =>
            IsUnit (finiteLocusFromCoord k n (MvPolynomial.X n)) ∧
              ∀ j : ℕ, j < n → finiteLocusFromCoord k n (MvPolynomial.X j) = 0
        | StratumIndex.inf =>
            ∀ j : ℕ, Ideal.Quotient.mk (infinityIdeal k) (MvPolynomial.X j) = 0) :=
  sorry

/-- Example 101.29.2 (3): each finite stratum `𝒳_i` is a gerbe over a scheme with group
`μ_{p^i}`. -/
@[stacks 06RE]
theorem isGerbeOver_rootsOfUnity_source (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : ℕ) :
    ∃ (Y : Over (base k))
      (f : (stratum k p hp (StratumIndex.ofNat i)).Y ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (finiteLocusStabilizer k p i ≅ finiteLocusRootsOfUnity k p i hp) :=
  sorry

/-- Example 101.29.2 (4): the infinite stratum `𝒳_∞` is a gerbe over a scheme with group
`𝔾ₘ`. -/
@[stacks 06RE]
theorem isGerbeOver_multiplicativeGroup_source (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) :
    ∃ (Y : Over (base k))
      (f : (stratum k p hp StratumIndex.inf).Y ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (infinityLocusStabilizer k p ≅ infinityLocusMultiplicativeGroup k) :=
  sorry

/-- Example 101.29.2 (5): the strata partition the points of `𝒳`. -/
@[stacks 06RE]
theorem isStratification_source (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (∀ x : Points (stack k p hp),
        ∃ i : StratumIndex, x ∈ Set.range (Points.map (stratum k p hp i).ι)) ∧
      Pairwise fun i j : StratumIndex ↦
        Disjoint (Set.range (Points.map (stratum k p hp i).ι))
          (Set.range (Points.map (stratum k p hp j).ι)) :=
  sorry

/-- Example 101.29.2 (6): this stratification is coarsest with the same properties; in
particular `𝒳` admits no finite stratification by reduced locally closed gerbe
substacks. -/
@[stacks 06RE]
theorem isCoarsest_source (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (Y : LocallyClosedSubstack (stack k p hp)) (I : Set StratumIndex)
    (h_reduced : AlgebraicStack.IsReduced Y.Y)
    (h_nonempty : I.Nonempty)
    (h_gerbe : ∃ (S : Over (base k)) (f : Y.Y ⟶ GroupoidsOver.slice S),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f)
    (h_union : Set.range (Points.map Y.ι) =
      ⋃ i ∈ I, Set.range (Points.map (stratum k p hp i).ι)) :
    ∃ i : StratumIndex, I = {i} :=
  sorry
