/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.EmbeddingDimensionTwo

/-!
# Cohen–Macaulay rings of dimension one and embedding dimension two

The six clauses identify the regularity, maximal-ideal power, existence,
relation-ideal, and Hilbert-function statements for a cotangent linear form
relatively prime to the eventual homogeneous relation.
-/

@[expose] public section

universe u

open IsLocalRing MvPolynomial

/- Exercise 111.28.8 (1): a lift of a cotangent linear form relatively prime to `F`
is a nonzerodivisor. -/
@[stacks 02EM] #check (IsLocalRing.isSMulRegular_of_isLinearFormClass :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F), IsSMulRegular A (z : A))

/- Exercise 111.28.8 (2): the maximal-ideal power formula holds for all sufficiently
large exponents, with `d = F.totalDegree`. -/
@[stacks 02EM] #check (IsLocalRing.maximalIdeal_pow_eq_span_pow_mul_pow_eventually :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F),
    ∃ N ≥ F.totalDegree, ∀ n ≥ N,
      maximalIdeal A ^ n = Ideal.span {(z : A)} ^ (n + 1 - F.totalDegree) *
        maximalIdeal A ^ (F.totalDegree - 1))

/- Exercise 111.28.8 (3): an infinite residue field guarantees the existence of a
lift whose cotangent linear form is relatively prime to `F`. -/
@[stacks 02EM] #check (IsLocalRing.exists_isLinearFormClass_isRelPrime :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Module.CohenMacaulay A A] [Infinite (ResidueField A)] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F),
    ∃ (z : maximalIdeal A) (α β : ResidueField A),
      IsLinearFormClass x α β z ∧ IsRelPrime (linearForm α β) F)

/- Exercise 111.28.8 (4): for the selected lift, the maximal-ideal power formula
holds for every exponent at least `F.totalDegree`. -/
@[stacks 02EM] #check (IsLocalRing.maximalIdeal_pow_eq_span_pow_mul_pow :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) {n : ℕ} (hn : F.totalDegree ≤ n),
    maximalIdeal A ^ n = Ideal.span {(z : A)} ^ (n + 1 - F.totalDegree) *
      maximalIdeal A ^ (F.totalDegree - 1))

/- Exercise 111.28.8 (5): the associated-graded presentation relation ideal is `(F)`. -/
@[stacks 02EM] #check (IsLocalRing.associatedGradedRelIdeal_eq_span :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F),
    associatedGradedRelIdeal x = Ideal.span {F})

/- Exercise 111.28.8 (6): the positive-degree Hilbert function takes the values
`2, 3, …, d - 1, d, d, …`, namely `min (n + 1) F.totalDegree`. -/
@[stacks 02EM] #check (IsLocalRing.associatedGradedHilbertFn_eq_min_succ_totalDegree :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) {n : ℕ} (hn : 1 ≤ n),
    associatedGradedHilbertFn A n = min (n + 1) F.totalDegree)
