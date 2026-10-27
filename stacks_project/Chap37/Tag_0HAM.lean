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

/- Lemma (0HAM). Formal étaleness is equivalent to point-local formal étaleness,
formal étaleness of the section-ring maps for every compatible affine pair,
and formal étaleness on some compatible affine coverings. -/
@[stacks 0HAM] #check
  (AlgebraicGeometry.FormallyEtale.local_criteria : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    List.TFAE [
      FormallyEtale f,
      ∀ x : X, ∃ (U : X.Opens) (V : Y.Opens) (_ : x ∈ U) (_ : f x ∈ V)
        (e : U ≤ f ⁻¹ᵁ V), FormallyEtale (f.resLE V U e),
      ∀ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
        (e : U ≤ f ⁻¹ᵁ V), (f.appLE V U e).hom.FormallyEtale,
      ∃ (𝒱 : Y.AffineOpenCover)
        (𝒰 : ∀ j : 𝒱.I₀, (f ⁻¹ᵁ (𝒱.f j).opensRange).toScheme.AffineOpenCover),
        ∀ (j : 𝒱.I₀) (i : (𝒰 j).I₀),
          (((𝒰 j).f i ≫ (f ∣_ (𝒱.f j).opensRange)).appTop.hom).FormallyEtale
    ])
