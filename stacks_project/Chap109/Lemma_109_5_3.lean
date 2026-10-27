/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StructureMorphism
import StacksCheckRecall

/-!
# Lemma 109.5.3

The structure morphism of `Curves` is quasi-separated and locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open scoped Bicategory

noncomputable section

universe u

/- Lemma 109.5.3 (1): the canonical morphism from the stack of curves to
Spec(ℤ) is quasi-separated. -/
@[stacks 0DSS] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instQuasiSeparated_toIdentitySlice
    (Spec (.of (ULift.{u} ℤ))) :
    CohStack.Hom.QuasiSeparated
      (CohStack.toIdentitySlice (Curves.toGroupoids (Spec (.of (ULift.{u} ℤ))))))

/- Lemma 109.5.3 (2): the canonical morphism from the stack of curves to
Spec(ℤ) is locally of finite presentation. -/
@[stacks 0DSS] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instLocallyOfFinitePresentation_toIdentitySlice
    (Spec (.of (ULift.{u} ℤ))) :
    CohStack.Hom.LocallyOfFinitePresentation
      (CohStack.toIdentitySlice (Curves.toGroupoids (Spec (.of (ULift.{u} ℤ))))))
