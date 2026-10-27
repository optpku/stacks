/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.Strata
import StacksCheckRecall

/-!
# Example 101.29.2

The weighted `𝔾ₘ`-action on infinite affine space over a field yields an algebraic stack
`[U / 𝔾ₘ]` with an infinite stratification by reduced locally closed gerbes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
open AlgebraicGeometry.Groupoids.Hom FiberedCategoryOver.Groupoids.Hom
open scoped AlgebraicGeometry Bicategory

universe u

/- Example 101.29.2 (1): for a field `k` and a prime `p`, the quotient
of the action `t · x_i = t^(p^i) x_i` on `Spec(k[x_i | i : ℕ])` is an algebraic stack. -/
@[stacks 06RE]
#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.instAlgebraicStack :
  ∀ (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p),
    AlgebraicStack (stack k p hp))

/- Example 101.29.2 (2): the quotient strata are reduced locally closed substacks.
The finite locus has its first `i` coordinates zero and `x_i` invertible;
the infinite locus has every coordinate zero. -/
@[stacks 06RE]
#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.instIsReducedStratumStack :
  ∀ (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex),
    AlgebraicStack.IsReduced (stratumStack k p hp i))

#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.instImmersionStratumι :
  ∀ (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex),
    Immersion (stratumι k p hp i))

#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.instIsReducedLocus :
  ∀ (k : Type u) [Field k] (i : StratumIndex),
    AlgebraicGeometry.IsReduced (locus k i).left)

#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.locus_finite :
  ∀ (k : Type u) [Field k] (i : ℕ),
    locus k (StratumIndex.ofNat i) = finiteLocus k i)

#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.locus_infinity :
  ∀ (k : Type u) [Field k],
    locus k StratumIndex.inf = infinityLocus k)

#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.finiteLocus_X_isUnit :
  ∀ (k : Type u) [Field k]
    (i : ℕ),
    IsUnit (finiteLocusFromCoord k i (MvPolynomial.X i)))

#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.finiteLocus_X_eq_zero :
  ∀ (k : Type u) [Field k]
    (i : ℕ) (j : ℕ) (hj : j < i),
    finiteLocusFromCoord k i (MvPolynomial.X j) = 0)

#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.infinityLocus_X_eq_zero :
  ∀ (k : Type u) [Field k],
    ∀ j : ℕ, Ideal.Quotient.mk (infinityIdeal k) (MvPolynomial.X j) = 0)

/- Example 101.29.2 (3): each finite stratum is a gerbe over a scheme with
stabilizer group scheme `μ_(p^i)`. -/
@[stacks 06RE]
#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.isGerbeOver_rootsOfUnity :
  ∀ (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : ℕ),
    ∃ (Y : Over (base k))
      (f : stratumStack k p hp (StratumIndex.ofNat i) ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (finiteLocusStabilizer k p i ≅ finiteLocusRootsOfUnity k p i hp))

/- Example 101.29.2 (4): the infinite stratum is a gerbe over a scheme with
multiplicative stabilizer group scheme. -/
@[stacks 06RE]
#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.isGerbeOver_multiplicativeGroup :
  ∀ (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p),
    ∃ (Y : Over (base k))
      (f : stratumStack k p hp StratumIndex.inf ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (infinityLocusStabilizer k p ≅ infinityLocusMultiplicativeGroup k))

/- Example 101.29.2 (5): the quotient-stratum images partition the ambient points. -/
@[stacks 06RE]
#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.isStratification :
  ∀ (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p),
    (∀ x : Points (stack k p hp),
        ∃ i : StratumIndex, x ∈ Set.range (Points.map (stratumι k p hp i))) ∧
      Pairwise fun i j : StratumIndex ↦
        Disjoint (Set.range (Points.map (stratumι k p hp i)))
          (Set.range (Points.map (stratumι k p hp j))))

/- Example 101.29.2 (6): a reduced locally closed gerbe whose image is a nonempty
union of the specified strata contains exactly one of these strata. -/
@[stacks 06RE]
#check (AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.isCoarsest :
  ∀ (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (Z : GroupoidsOver (base k)) [AlgebraicStack Z]
    (f : Z ⟶ stack k p hp) [Immersion f] (I : Set StratumIndex)
    (h_reduced : AlgebraicStack.IsReduced Z)
    (h_nonempty : I.Nonempty)
    (h_gerbe : ∃ (S : Over (base k)) (g : Z ⟶ GroupoidsOver.slice S),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) g)
    (h_union : Set.range (Points.map f) =
      ⋃ i ∈ I, Set.range (Points.map (stratumι k p hp i))),
    ∃ i : StratumIndex, I = {i})
