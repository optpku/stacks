/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern

/-!
# Invertible-subsheaf additivity of total Chern classes

A short exact sequence `0 ⟶ L ⟶ E ⟶ F ⟶ 0` with
`L` invertible and `E`, `F` finite locally free of ranks `r`, `r - 1`
yields `c(E) = c(L) c(F)` in `A^*(X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.OperationalChow
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- A short exact sequence with invertible submodule and finite locally free middle and quotient modules satisfies the total Chern product formula. -/
theorem total_eq_mul_of_invertible_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (L E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [isInvertibleObject L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : L ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact) :
    (∑ i : Fin (r + 1), homogeneous δ f i.val (chernClass δ f E i.val)) =
      (∑ i : Fin 2, homogeneous δ f i.val (chernClass δ f L i.val)) *
        (∑ i : Fin ((r - 1) + 1), homogeneous δ f i.val (chernClass δ f F i.val)) :=
  sorry

/-- Whitney component form of invertible-subsheaf additivity:
`c_i(E) = c_i(F) + c₁(L) * c_{i-1}(F)` in `A^*(X)`, reading the second
summand as `0` when `i = 0`. -/
theorem component_eq_add_of_invertible_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (L E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [isInvertibleObject L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : L ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)
    (i : ℕ) (hi : i ≤ r) :
    homogeneous δ f i (chernClass δ f E i) =
      homogeneous δ f i (chernClass δ f F i) +
        (if h : 0 < i then
          ringClass f δ L * homogeneous δ f (i - 1 : ℕ) (chernClass δ f F (i - 1))
        else 0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
