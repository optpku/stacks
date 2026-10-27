/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Hilbert
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative

/-!
# Separatedness and finite presentation of Hilbert Quot loci

The fixed Hilbert locus for a finitely presented module and a relatively ample
invertible module is represented by an algebraic space separated and of finite
presentation over the base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The Hilbert Quot locus for a finitely presented module and a relatively ample
invertible module along a separated morphism of finite presentation is separated
over the base. -/
instance instIsSeparatedOverQuotHilbert {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f] (F L : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] [isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] (P : ℤ → ℤ) :
    IsSeparatedOver (quotHilbert f F L P).toFunctor := sorry

/-- The Hilbert Quot locus for a finitely presented module and a relatively ample
invertible module along a separated morphism of finite presentation is of finite
presentation over the base. -/
theorem quotHilbert_isFinitePresentationOver {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    [isInvertibleObject L] [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L]
    (P : ℤ → ℤ) :
    IsFinitePresentationOver (quotHilbert f F L P).toFunctor := sorry

/-- The Hilbert Quot locus for a finitely presented module and a relatively ample
invertible module along a separated morphism of finite presentation is represented
by a single morphism that is separated and of finite presentation over the base. -/
theorem quotHilbert_exists_separated_finitePresentation {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    [isInvertibleObject L] [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L]
    (P : ℤ → ℤ) :
    ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
      Separated π ∧ FinitePresentation π ∧
        Nonempty ((quotHilbert f F L P).toFunctor ≅ yonedaOver π) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
