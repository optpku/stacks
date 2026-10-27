/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Representability
import StacksCheckRecall

/-!
# Lemma 108.7.2

The structure morphism of the Grothendieck Hilbert functor over `B` is
separated and locally of finite presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.7.2 (1): the structure morphism of `hilbert f` over `B` is
separated. -/
@[stacks 0DM7] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.instIsSeparatedOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [Separated f], AlgebraicGeometry.AlgebraicSpace.Quot.IsSeparatedOver
      (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert f))

/- Lemma 108.7.2 (2): the structure morphism of `hilbert f` over `B` is
locally of finite presentation. -/
@[stacks 0DM7] #check
  (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert_isLocallyOfFinitePresentationOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
      [Separated f], IsLocallyOfFinitePresentationOver
        (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert f))
