/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.HilbertFinitePresentation

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
  [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
  [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] (P : ℤ → ℤ)

/-- For a separated morphism of finite presentation of algebraic spaces and a
relatively ample invertible module, the Hilbert-polynomial locus is represented
by one morphism that is separated and of finite presentation over the base. -/
theorem hilbertPolynomial_exists_separated_finitePresentation :
    ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
      Separated π ∧ FinitePresentation π ∧
        Nonempty
          ((Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor ≅
            yonedaOver π) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
