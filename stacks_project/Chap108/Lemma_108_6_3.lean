/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Proper
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Quot CategoryTheory.MonoidalCategory

universe u

/- Lemma 108.6.3: For a proper finitely presented morphism of algebraic spaces,
a finitely presented module F, an invertible relatively ample module L, and a
numerical Hilbert polynomial P, the Hilbert Quot algebraic space is proper over
the base. -/
@[stacks 0DPC] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert_isProperOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [Proper f] [FinitePresentation f] (F L : X.Modules)
      [F.IsFinitePresentation] [isInvertibleObject L]
      [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L]
      (P : ℤ → ℤ) (hP : IsNumericalPolynomial P),
      IsProperOver (quotHilbert f F L P).toFunctor)
