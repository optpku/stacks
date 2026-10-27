/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormalLocality
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
universe u

/- Lemma (0HAL). Formal unramifiedness is equivalent to its point-local,
affine-local, and affine-cover criteria. -/
@[stacks 0HAL] #check
  (AlgebraicGeometry.FormallyUnramified.local_criteria : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    List.TFAE [
      FormallyUnramified f,
      ∀ x : X, ∃ (U : X.Opens) (V : Y.Opens) (_ : x ∈ U) (_ : f x ∈ V)
        (e : U ≤ f ⁻¹ᵁ V), FormallyUnramified (f.resLE V U e),
      ∀ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
        (e : U ≤ f ⁻¹ᵁ V), (f.appLE V U e).hom.FormallyUnramified,
      ∃ (𝒱 : Y.AffineOpenCover)
        (𝒰 : ∀ j : 𝒱.I₀, (f ⁻¹ᵁ (𝒱.f j).opensRange).toScheme.AffineOpenCover),
        ∀ (j : 𝒱.I₀) (i : (𝒰 j).I₀),
          (((𝒰 j).f i ≫ (f ∣_ (𝒱.f j).opensRange)).appTop.hom).FormallyUnramified
    ])
