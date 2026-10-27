/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Sheaf

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.9.3: for a finitely presented morphism `f : X ⟶ B` of algebraic spaces
and any algebraic space `T` over `S`, the canonical pullback map identifies Hilbert
pairs `(h, Z)` with morphisms from the fppf sheaf of points of `T` to `Hilb_{X/B}`. -/
@[stacks 0D3W] #check
  (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertSheafHom_bijective :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
      (T : AlgebraicSpace S),
      Function.Bijective (AlgebraicGeometry.AlgebraicSpace.Hilbert.toHilbertSheafHom f T))
