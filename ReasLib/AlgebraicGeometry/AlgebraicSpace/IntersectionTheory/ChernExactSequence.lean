/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.GradedRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Noetherian

/-!
# Chern classes of short exact sequences

Total operational Chern classes multiply in short exact sequences of finite
locally free modules, and their components satisfy the corresponding
convolution formula. A trivial rank-one submodule forces the top Chern class
to vanish and identifies lower components with those of the quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- The top operational Chern class vanishes for a short exact sequence with a
trivial rank-one submodule. -/
theorem top_eq_zero_of_unit_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : 𝟙_ X.Modules ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact) :
    chernClass δ f E r = OperationalChow.zero δ f (r : ℤ) :=
  sorry

/-- The Chern class components below the rank agree across a short exact
sequence with a trivial rank-one submodule. -/
theorem component_eq_of_unit_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : 𝟙_ X.Modules ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)
    (j : ℕ) (hj : j < r) :
    chernClass δ f E j = chernClass δ f F j :=
  sorry

/-- The total operational Chern class of the middle term of a short exact
sequence of finite locally free modules is the ordered product of the total
operational Chern classes of its endpoints. -/
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
    (∑ i : Fin (r₁ + r₂ + 1), OperationalChow.homogeneous δ f i.val (chernClass δ f E i.val)) =
      (∑ i : Fin (r₁ + 1), OperationalChow.homogeneous δ f i.val (chernClass δ f E₁ i.val)) *
        (∑ i : Fin (r₂ + 1), OperationalChow.homogeneous δ f i.val (chernClass δ f E₂ i.val)) :=
  sorry

/-- Each operational Chern class component of the middle term of a short
exact sequence of finite locally free modules is the convolution of the
endpoint Chern class components in the operational Chow ring. -/
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
    OperationalChow.homogeneous δ f i (chernClass δ f E i) =
      ∑ j : Fin (i + 1),
        OperationalChow.homogeneous δ f j.val (chernClass δ f E₁ j.val) *
          OperationalChow.homogeneous δ f (i - j.val : ℕ) (chernClass δ f E₂ (i - j.val)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
