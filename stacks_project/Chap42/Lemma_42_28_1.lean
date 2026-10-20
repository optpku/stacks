/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Commutativity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.28.1: for two invertible modules on an integral scheme, intersecting the
relative divisor cycle of either chosen nonzero meromorphic section with the first Chern
class of the other module gives the same class. Taking `k = n - 2` recovers the source
indexing in `CH_{n - 2}(X)`. -/
@[stacks 02TH] #check
  (AlgebraicGeometry.Scheme.Modules.firstChernClassCap_relativeDivisorCycle_comm :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (k : ℤ)
      (hX : p.relativeDimensionFunction δ (genericPoint X) = (k + 1) + 1)
      (ℒ 𝒩 : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
        [AlgebraicGeometry.Scheme.Modules.Invertible 𝒩]
        (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
        (t : X.toLocallyRingedSpace.meromorphicSections 𝒩) (hs : s ≠ 0) (ht : t ≠ 0),
      AlgebraicGeometry.Scheme.Modules.firstChernClassCap p δ 𝒩 k
          (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorCycle
            p δ ℒ s hs (k + 1) hX) =
        AlgebraicGeometry.Scheme.Modules.firstChernClassCap p δ ℒ k
          (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorCycle
            p δ 𝒩 t ht (k + 1) hX))
