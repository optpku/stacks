/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 108.7.8

The Hilbert-polynomial algebraic space of closed subschemes, taken with
respect to a relatively ample invertible module, is separated of finite
presentation over the base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 108.7.8: the fixed Hilbert-polynomial locus for a relatively ample
invertible module is represented by a separated morphism of finite presentation. -/
@[stacks 0DPI] #check
  (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbertPolynomial_exists_separated_finitePresentation :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [FinitePresentation f] → [Separated f] → ∀ (L : X.Modules),
      [isInvertibleObject L] → [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] →
      ∀ (P : ℤ → ℤ), ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        Separated π ∧ FinitePresentation π ∧
          Nonempty
            ((Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor ≅
              yonedaOver π))
