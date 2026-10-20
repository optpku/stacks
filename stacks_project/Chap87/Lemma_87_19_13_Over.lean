/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineEtaleOver
public import stacks_project.Chap87.Lemma_87_34_6_Over

/-! # Affine étale slice compatibility

The affine-domain full subcategory and its concrete constructors are supplied by the shared library.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.AffineEtaleOver :
  ∀ {S : Scheme.{u}} (Y : (Over S)ᵒᵖ ⥤ Type u), Type (u + 1))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.AffineEtaleOver.mk :
  ∀ {S : Scheme.{u}} {Y U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ Y)
    [FormalAlgebraicSpace.Etale φ],
    (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U) → AffineEtaleOver Y)
