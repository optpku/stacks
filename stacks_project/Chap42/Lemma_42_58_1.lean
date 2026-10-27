/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Chow
import StacksCheckRecall

/-!
# Lemma 42.58.1

On a quasi-compact regular finite-type scheme over `S` with affine diagonal and
bounded relative dimension, Chern character followed by cap against `[X]` is an
isomorphism `K₀(Vect(X)) ⊗ ℚ ≃ CH_*(X) ⊗ ℚ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 42.58.1: On a quasi-compact regular finite-type scheme over `S` with affine
absolute diagonal and bounded relative dimension, the canonical Chern character followed
by cap against `[X]` is an isomorphism on rational vector-bundle `K₀`. -/
@[stacks 0FEY] #check (AlgebraicGeometry.Scheme.VectorBundleK0.toRationalChow_bijective :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [Scheme.Hom.FiniteType X.hom] [CompactSpace X.left] [Scheme.Regular X.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)),
    Function.Bijective
      (AlgebraicGeometry.Scheme.VectorBundleK0.toRationalChow_tensorQ δ X
        (ChernClass.Theory.canonical δ X.hom) hδ))
