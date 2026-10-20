/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Dimension-shifted flat base change sends rational boundaries to rational boundaries. -/
#check
  (AlgebraicGeometry.RationalEquivalence.baseChangePullback_mem_boundaries :
    ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
      (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
      (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ),
      @AlgebraicGeometry.RationalEquivalence.boundaries X
          (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k ≤
        (@AlgebraicGeometry.RationalEquivalence.boundaries (pullback f g)
          (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
          ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c)).comap
          (AlgebraicGeometry.CycleGroup.baseChangePullback g δ δ' c hcompat f k))

/- Lemma 42.67.4: in Situation 42.67.1, dimension-shifted flat base change
descends to an additive homomorphism from degree-`k` Chow groups of `X` to
degree-`k + c` Chow groups of its canonical pullback to `S'`. -/
@[stacks 0FVJ] #check
  (AlgebraicGeometry.ChowGroup.baseChangePullback :
    ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
      (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
      (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ),
      @AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k →+
        @AlgebraicGeometry.ChowGroup (pullback f g)
          (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
          ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c))

/- Dimension-shifted flat base change on Chow groups is computed on cycle
representatives by cycle-level base change followed by passage to the Chow class. -/
#check
  (AlgebraicGeometry.ChowGroup.baseChangePullback_chowClass :
    ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
      (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
      (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
      (α : AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k),
      AlgebraicGeometry.ChowGroup.baseChangePullback g δ δ' c hcompat f k
          (@AlgebraicGeometry.chowClass X (LocallyOfFiniteType.isLocallyNoetherian f)
            (f.relativeDimensionFunction δ) inferInstance k α) =
        @AlgebraicGeometry.chowClass (pullback f g)
          (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
          ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c)
          (AlgebraicGeometry.CycleGroup.baseChangePullback g δ δ' c hcompat f k α))
