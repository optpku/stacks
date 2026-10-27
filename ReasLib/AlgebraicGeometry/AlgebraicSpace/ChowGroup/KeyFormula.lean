/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.MeromorphicSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RationalEquivalence

/-! # The key formula for meromorphic-section divisors on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.PrimeDivisor

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- For regular meromorphic sections of two invertible modules on an integral
algebraic space of `δ`-dimension `n`, the locally finite sum of pushed-forward
order-weighted restricted-generator divisor differences equals the boundary of
their henselian tame symbols, provided the prime divisors include every locus
where either section fails to generate the henselian fibre. -/
theorem keyFormula {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    {I : Type v} (Z : I → PrimeDivisor X) (hZ : Injective Z)
    (hlocal : LocallyFinite fun i ↦ ((Z i).pointsSet : Set (Points X)))
    (hsAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) → GeneratesHenselianFibre s W)
    (htAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) → GeneratesHenselianFibre t W)
    (sData : ∀ i, KeyFormulaPresentation.LocalPresentation s (Z i))
    (tData : ∀ i, KeyFormulaPresentation.LocalPresentation t (Z i)) :
    AlgebraicCycle.locallyFiniteSum
        (fun i ↦ keyFormulaTerm f δ n hX L N (Z i) s hs t ht (sData i) (tData i))
        (keyFormulaTermsLocallyFinite f δ n hX L N Z s hs t ht hlocal sData tData) =
      (RationalEquivalence.boundary f δ (n - 2) (fun i ↦ (Z i).subspace)
          (fun i ↦ PrimeDivisor.instIsIntegral_space (Z i))
          (fun i ↦ primeDivisor_deltaDimension f δ n hX (Z i))
          (fun i ↦ tameSymbolOnSpace_ofGood f (Z i)
            (sData i).fraction
            (tData i).fraction) hlocal :
        Function.locallyFinsupp (Points X) ℤ) :=
  sorry

/-- The locally finite sum of order-weighted restricted-generator divisor
differences on an integral algebraic space of `δ`-dimension `n` is an
`(n - 2)`-cycle. -/
theorem keyFormula_mem_cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    {I : Type v} (Z : I → PrimeDivisor X)
    (hlocal : LocallyFinite fun i ↦ ((Z i).pointsSet : Set (Points X)))
    (sData : ∀ i, KeyFormulaPresentation.LocalPresentation s (Z i))
    (tData : ∀ i, KeyFormulaPresentation.LocalPresentation t (Z i)) :
    AlgebraicCycle.locallyFiniteSum
        (fun i ↦ keyFormulaTerm f δ n hX L N (Z i) s hs t ht (sData i) (tData i))
        (keyFormulaTermsLocallyFinite f δ n hX L N Z s hs t ht hlocal sData tData) ∈
      cycleGroup f δ (n - 2) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
