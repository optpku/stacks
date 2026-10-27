/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Nodal.Smooth
import StacksCheckRecall

/-!
# Smoothness of the structure morphism of nodal curves

The open substack `𝒞urves^{nodal} ⊂ 𝒞urves` has smooth structure morphism to
`Spec(Z)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.18.2: the structure morphism `𝒞urves^{nodal} ⟶ Spec(Z)` is smooth. -/
@[stacks 0E00] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_nodal :
    ∀ (S : Scheme.{u}), CohStack.Hom.Smooth
      (inclusionOf (nodal S) ≫ CohStack.toIdentitySlice (toGroupoids S)))
