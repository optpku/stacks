/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import stacks_project.Chap82.Lemma_82_30_2

/-!
# Additivity of total Chern classes

In Situation 82.2.1, a short exact sequence `0 ⟶ E₁ ⟶ E ⟶ E₂ ⟶ 0` of
finite locally free sheaves of ranks `r₁`, `r₁ + r₂`, `r₂` yields
`c(E) = c(E₁) * c(E₂)` in `A^*(X)`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.ChowCohomology
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- Lemma 82.30.3: In Situation 82.2.1 let `X / B` be good. Suppose that
`E` sits in an exact sequence `0 ⟶ E₁ ⟶ E ⟶ E₂ ⟶ 0` of finite locally
free sheaves of ranks `r₁`, `r₁ + r₂`, `r₂`. The total Chern classes
satisfy `c(E) = c(E₁) * c(E₂)` in `A^*(X)`. -/
@[stacks 0ES9]
theorem total_eq_mul_of_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E₁ E E₂ : X.Modules) (r₁ r₂ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₁ E₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r₁ + r₂) E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₂ E₂]
    (ι : E₁ ⟶ E) (q : E ⟶ E₂)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact) :
    (∑ i : Fin (r₁ + r₂ + 1), homogeneous δ f i.val (chernClass δ f E i.val)) =
      (∑ i : Fin (r₁ + 1), homogeneous δ f i.val (chernClass δ f E₁ i.val)) *
        (∑ i : Fin (r₂ + 1), homogeneous δ f i.val (chernClass δ f E₂ i.val)) :=
  sorry

/-- Whitney component form of additivity of total Chern classes:
the degree-`i` summand of `c(E)` equals
`∑ j, c_j(E₁) * c_{i - j}(E₂)` in `A^*(X)`. -/
theorem component_eq_sum_of_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E₁ E E₂ : X.Modules) (r₁ r₂ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₁ E₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r₁ + r₂) E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₂ E₂]
    (ι : E₁ ⟶ E) (q : E ⟶ E₂)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)
    (i : ℕ) (hi : i ≤ r₁ + r₂) :
    homogeneous δ f i (chernClass δ f E i) =
      ∑ j : Fin (i + 1),
        homogeneous δ f j.val (chernClass δ f E₁ j.val) *
          homogeneous δ f (i - j.val : ℕ) (chernClass δ f E₂ (i - j.val)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
