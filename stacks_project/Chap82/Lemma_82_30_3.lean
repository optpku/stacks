/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernExactSequence

/-!
# Additivity of total Chern classes

In Situation 82.2.1, a short exact sequence `0 ⟶ E₁ ⟶ E ⟶ E₂ ⟶ 0` of
finite locally free sheaves of ranks `r₁`, `r₁ + r₂`, `r₂` yields
`c(E) = c(E₁) * c(E₂)` in `A^*(X)`.
-/

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open scoped BigOperators

universe u

/- Lemma 82.30.3: The total Chern class of a finite locally free short exact
sequence is the product of the total Chern classes of its endpoints. -/
@[stacks 0ES9] #check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.total_eq_mul_of_shortExact :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E₁ E E₂ : X.Modules) (r₁ r₂ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₁ E₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r₁ + r₂) E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₂ E₂]
    (ι : E₁ ⟶ E) (q : E ⟶ E₂)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact),
    (∑ i : Fin (r₁ + r₂ + 1), OperationalChow.homogeneous δ f i.val (chernClass δ f E i.val)) =
      (∑ i : Fin (r₁ + 1), OperationalChow.homogeneous δ f i.val (chernClass δ f E₁ i.val)) *
        (∑ i : Fin (r₂ + 1), OperationalChow.homogeneous δ f i.val (chernClass δ f E₂ i.val)))

#check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.component_eq_sum_of_shortExact :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E₁ E E₂ : X.Modules) (r₁ r₂ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₁ E₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r₁ + r₂) E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r₂ E₂]
    (ι : E₁ ⟶ E) (q : E ⟶ E₂)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)
    (i : ℕ) (hi : i ≤ r₁ + r₂),
    OperationalChow.homogeneous δ f i (chernClass δ f E i) =
      ∑ j : Fin (i + 1),
        OperationalChow.homogeneous δ f j.val (chernClass δ f E₁ j.val) *
          OperationalChow.homogeneous δ f (i - j.val : ℕ) (chernClass δ f E₂ (i - j.val)))
