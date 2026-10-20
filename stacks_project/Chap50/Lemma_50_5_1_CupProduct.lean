/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeCupProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

#check (AlgebraicGeometry.Scheme.DeRham.hodgeCupProduct :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Monoidal]
    [(globalDerivedFunctor f).LaxMonoidal],
    CoefficientTensorModel f → (a b : ℕ) → (i j : ℤ) →
      hodgeCohomologyObject f a i ⊗ hodgeCohomologyObject f b j ⟶
        hodgeCohomologyObject f (a + b) (i + j))

#check (AlgebraicGeometry.Scheme.DeRham.canonicalHodgeCupProduct :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Monoidal]
    [(globalDerivedFunctor f).LaxMonoidal]
    (a b : ℕ) (i j : ℤ),
    hodgeCohomologyObject f a i ⊗ hodgeCohomologyObject f b j ⟶
      hodgeCohomologyObject f (a + b) (i + j))

end AlgebraicGeometry.Scheme.DeRham
