/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.KernelCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 57.14.1: base change along `g : S' ⟶ S` sends the Fourier--Mukai kernel category of
smooth proper schemes over `S` to the corresponding category over `S'`, with object map given by
scheme pullback and morphism map given by derived pullback of perfect-kernel classes. -/
@[stacks 0G0G]
#check (fourierMukaiKernelBaseChange :
  ∀ {S S' : Scheme.{u}} (g : S' ⟶ S),
    FourierMukaiObject S ⥤ FourierMukaiObject S')

/- The promoted base-change functor acts on objects by canonical scheme pullback. -/
#check (fourierMukaiKernelBaseChange_obj :
  ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) (X : FourierMukaiObject S),
    (fourierMukaiKernelBaseChange g).obj X =
      FourierMukaiObject.baseChange g X)
