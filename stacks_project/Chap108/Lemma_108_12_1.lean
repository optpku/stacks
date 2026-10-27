/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Diagonal

/-!
# Lemma 108.12.1

The relative diagonal of the stack of complexes over `B` is affine and of
finite presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

/- Lemma 108.12.1 (1): the relative diagonal of the stack of relatively perfect
complexes with vanishing negative fibre self-Ext over `B` is affine. -/
@[stacks 0DPW] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.instAffine_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    CohStack.Hom.Affine
      (CohStack.Hom.diagonal (AlgebraicGeometry.AlgebraicSpace.Complexes.toBase f)))

/- Lemma 108.12.1 (2): the relative diagonal of the stack of relatively perfect
complexes with vanishing negative fibre self-Ext over `B` is of finite presentation. -/
@[stacks 0DPW] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.instFinitePresentation_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    CohStack.Hom.FinitePresentation
      (CohStack.Hom.diagonal (AlgebraicGeometry.AlgebraicSpace.Complexes.toBase f)))
