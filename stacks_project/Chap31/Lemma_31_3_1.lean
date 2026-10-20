/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.TensorPullback

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.3.1 (1): for quasi-coherent scheme modules `ℱ` and `𝒢`, with `ℱ` flat over
`f : X ⟶ S`, the relative associated points of `ℱ` lying over the associated points of `𝒢`
are associated points of `ℱ ⊗ f^*𝒢`. -/
@[stacks 05DB] #check (
  AlgebraicGeometry.Scheme.Modules.relativeAssassin.inter_preimage_subset_associatedPoints_tensor_pullback :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      (ℱ : X.Modules) (𝒢 : S.Modules)
      [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent],
      Scheme.Modules.flatOver ℱ f →
        Scheme.Modules.relativeAssassin f ℱ ∩
            f.base ⁻¹' Scheme.Modules.associatedPoints 𝒢 ⊆
          Scheme.Modules.associatedPoints
            (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢))

/- Lemma 31.3.1 (2): under the same hypotheses, if `S` is locally Noetherian, the associated
points of `ℱ ⊗ f^*𝒢` are exactly the relative associated points of `ℱ` lying over the associated
points of `𝒢`. -/
@[stacks 05DB] #check (
  AlgebraicGeometry.Scheme.Modules.relativeAssassin.associatedPoints_tensor_pullback_eq_inter_preimage :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      (ℱ : X.Modules) (𝒢 : S.Modules)
      [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
      (_ : Scheme.Modules.flatOver ℱ f) [IsLocallyNoetherian S],
        Scheme.Modules.associatedPoints
            (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢) =
          Scheme.Modules.relativeAssassin f ℱ ∩
            f.base ⁻¹' Scheme.Modules.associatedPoints 𝒢)
