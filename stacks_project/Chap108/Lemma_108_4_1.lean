/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Diagonal
import StacksCheckRecall

/-!
# Lemma 108.4.1

The relative diagonal of the stack of coherent sheaves over `B` is affine and of
finite presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open scoped Bicategory

universe u

/- Lemma 108.4.1 (1): the relative diagonal of the stack of coherent sheaves
for a separated morphism of finite presentation is affine. -/
@[stacks 0DLY] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.instAffine_diagonal :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [FinitePresentation f] → [Separated f] →
        Hom.Affine (Hom.diagonal (forget f)))

/- Lemma 108.4.1 (2): the relative diagonal of the stack of coherent sheaves
for a separated morphism of finite presentation is of finite presentation. -/
@[stacks 0DLY] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.instFinitePresentation_diagonal :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [FinitePresentation f] → [Separated f] →
        Hom.FinitePresentation (Hom.diagonal (forget f)))
