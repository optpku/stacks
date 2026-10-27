/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable.Smooth
import StacksCheckRecall

/-!
# Smoothness of the structure morphisms of prestable curves

The structure morphisms `𝒞urves^{prestable} ⟶ Spec(Z)` and
`𝒞urves^{prestable}_g ⟶ Spec(Z)` are smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.20.4 (1): the structure morphism `𝒞urves^{prestable} ⟶ Spec(Z)` is
smooth. -/
@[stacks 0E6W] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_prestable :
    ∀ (S : Scheme.{u}), CohStack.Hom.Smooth
      (inclusionOf (prestable S) ≫ CohStack.toIdentitySlice (toGroupoids S)))

/- Lemma 109.20.4 (2): the structure morphism `𝒞urves^{prestable}_g ⟶ Spec(Z)` is
smooth. -/
@[stacks 0E6W] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_prestableOfGenus :
    ∀ (g : ℕ) (S : Scheme.{u}), CohStack.Hom.Smooth
      (inclusionOf (prestableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)))
