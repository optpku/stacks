/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.HilbertFinitePresentation
import StacksCheckRecall

/-!
# Lemma 108.6.4

The Hilbert Quot algebraic space of finitely presented quotients of a
finitely presented module, with Hilbert polynomial taken with respect to a
relatively ample invertible module, is separated of finite presentation over
the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 108.6.4: For a separated morphism f : X ⟶ B of finite presentation,
a finitely presented module F, and an invertible module L relatively ample on X/B,
the fixed Hilbert Quot locus is represented by one morphism π : Q ⟶ B that is
both separated and of finite presentation. -/
@[stacks 0DPD] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert_exists_separated_finitePresentation :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] [Separated f] (F L : X.Modules)
      [F.IsQuasicoherent] [F.IsFinitePresentation] [isInvertibleObject L]
      [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] (P : ℤ → ℤ),
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        Separated π ∧ FinitePresentation π ∧
          Nonempty ((Quot.quotHilbert f F L P).toFunctor ≅ yonedaOver π))
