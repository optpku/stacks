/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.LocallyOfFinitePresentation
import StacksCheckRecall

/-!
# Lemma 108.8.2

The structure morphism of the Picard stack over `B` is quasi-separated and
locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Picard
open scoped Bicategory

noncomputable section

universe u

/- Lemma 108.8.2 (1): the Picard stack structure morphism over `B` is
quasi-separated. -/
@[stacks 0DMB] #check (AlgebraicGeometry.AlgebraicSpace.Picard.toBase.quasiSeparated :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f],
    CohStack.Hom.QuasiSeparated (toBase f))

/- Lemma 108.8.2 (2): the Picard stack structure morphism over `B` is locally
of finite presentation. -/
@[stacks 0DMB] #check (AlgebraicGeometry.AlgebraicSpace.Picard.toBase.locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f],
    CohStack.Hom.LocallyOfFinitePresentation (toBase f))
