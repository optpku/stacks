/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.RingTheory.Polynomial.Numerical

/-!
# Finite presentation of numerical relative morphism loci

Relatively ample invertible modules polarize the numerical relative-Hom locus,
which is represented by a separated morphism of finite presentation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- For a flat proper morphism of finite presentation and a separated morphism
of finite presentation, relatively ample invertible modules on the two spaces
and a numerical polynomial determine a numerical relative-Hom locus, polarized
by their external tensor product, represented by one separated morphism of
finite presentation over the base. -/
theorem morNumericalHilbert_exists_separated_finitePresentation
    {S : Scheme.{u}} {Y B X : AlgebraicSpace S} (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y] [Separated x] [FinitePresentation x]
    (N : Y.Modules) (L : X.Modules) [isInvertibleObject N] [isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple y N]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple x L]
    (P : ℤ → ℤ) (hP : IsNumericalPolynomial P) :
    ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
      Separated π ∧ FinitePresentation π ∧
        Nonempty
          ((morNumericalHilbert y x (Modules.externalTensorProduct y x N L) P).toFunctor ≅
            yonedaOver π) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
