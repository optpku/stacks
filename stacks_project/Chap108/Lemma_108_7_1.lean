/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Diagonal
import StacksCheckRecall

/-!
# Lemma 108.7.1

The relative diagonal of the Grothendieck Hilbert functor over `B` is a closed
immersion of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 108.7.1 (1): the diagonal of `hilbert f` over `B` is a closed immersion. -/
@[stacks 0DM6]
#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.isClosedImmersion_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f],
    SchemeOver.IsClosedImmersion
      (Limits.diag (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert f)))

/- Lemma 108.7.1 (2): the diagonal of `hilbert f` over `B` is of finite
presentation. -/
@[stacks 0DM6]
#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.finitePresentation_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f],
    SchemeOver.IsFinitePresentation
      (Limits.diag (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert f)))
