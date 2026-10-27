/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.SplittingPrinciple
import StacksCheckRecall

/-! # Splitting principle for Chow groups of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v

/- Lemma 82.31.1: A finite family of finite locally free modules on a good algebraic
space admits a projective flat splitting morphism with universally injective Chow pullback
and invertible-quotient filtrations of the prescribed ranks. -/
@[stacks 0ESC] #check (AlgebraicGeometry.AlgebraicSpace.exists_projective_flat_splitting :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {ι : Type v} [Finite ι] (E : ι → X.Modules) (r : ι → ℕ)
    [∀ i, SheafOfModules.IsFiniteLocallyFreeOfRank (r i) (E i)],
    ∃ (P : AlgebraicSpace S) (π : P ⟶ X) (d : ℕ),
      Projective π ∧ Flat π ∧ RelativeDimension π d ∧
        QuasiSeparated (π ≫ pX) ∧ LocallyOfFiniteType (π ≫ pX) ∧
        Hom.UniversallyInjectivePullback pX δ π d ∧
        ∀ i, CategoryTheory.HasInvertibleQuotientFiltrationOfLength (r i)
          ((Modules.pullback π).obj (E i)))
