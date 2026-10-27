/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Numerical.FinitePresentation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 108.10.5. The numerical relative-Hom locus polarized by the external
 tensor product of relatively ample invertible modules is represented by a
 separated morphism of finite presentation over the base. -/
@[stacks 0DPR] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeHom.morNumericalHilbert_exists_separated_finitePresentation :
    ∀ {S : Scheme.{u}} {Y B X : AlgebraicSpace S} (y : Y ⟶ B) (x : X ⟶ B)
      [Flat y] [Proper y] [FinitePresentation y] [Separated x] [FinitePresentation x]
      (N : Y.Modules) (L : X.Modules) [isInvertibleObject N] [isInvertibleObject L]
      [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple y N]
      [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple x L]
      (P : ℤ → ℤ) (hP : IsNumericalPolynomial P),
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        Separated π ∧ FinitePresentation π ∧
          Nonempty
            ((RelativeHom.morNumericalHilbert y x
                (Modules.externalTensorProduct y x N L) P).toFunctor ≅ yonedaOver π))
