/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.MorphismProperties

/-!
# Lemma 108.12.2

The structure morphism of the stack of complexes over `B` is quasi-separated and
locally of finite presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

/- Lemma 108.12.2 (1): the structure morphism of the stack of relatively perfect
complexes with vanishing negative fibre self-Ext over `B` is quasi-separated. -/
@[stacks 0DPX] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.instQuasiSeparated_toBase :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    CohStack.Hom.QuasiSeparated (AlgebraicGeometry.AlgebraicSpace.Complexes.toBase f))

/- Lemma 108.12.2 (2): the structure morphism of the stack of relatively perfect
complexes with vanishing negative fibre self-Ext over `B` is locally of finite presentation. -/
@[stacks 0DPX] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.instLocallyOfFinitePresentation_toBase :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    CohStack.Hom.LocallyOfFinitePresentation
      (AlgebraicGeometry.AlgebraicSpace.Complexes.toBase f))
