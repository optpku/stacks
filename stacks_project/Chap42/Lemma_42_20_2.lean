/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 42.20.2: Flat pullback along a morphism of relative dimension `r` sends
rationally equivalent degree-`k` cycles to rationally equivalent degree-`k + r` cycles. -/
@[stacks 02S1] #check
  (AlgebraicGeometry.RationalEquivalence.flatPullback_mem_boundaries :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (k : ℤ),
      @AlgebraicGeometry.RationalEquivalence.boundaries Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance k ≤
        (@AlgebraicGeometry.RationalEquivalence.boundaries X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))).comap
          (AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r k))
