/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeCupProduct

/-!
# Elementwise Hodge cup products

The morphism-level Hodge cup product on coefficient-module cohomology induces an elementwise
product of classes, after transporting the sum of natural cohomological degrees along the
canonical integer cast.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal Functor.RightDerived.Homotopy
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/-- Monoidality of the unbounded derived-category quotient functor on coefficient modules. -/
public class CoefficientQhMonoidal (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)] where
  /-- The derived-category quotient functor is monoidal. -/
  [qh_monoidal :
    (DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Monoidal]

/-- The elementwise Hodge cup product of two cohomology classes, with the sum of natural
degrees transported along the canonical integer cast. -/
public noncomputable def hodgeCup (f : X ⟶ S)
    [derivedMonoidal : MonoidalCategory (coefficientDerived f)]
    [qhMonoidal : CoefficientQhMonoidal f]
    [globalLaxMonoidal : (globalDerivedFunctor f).LaxMonoidal]
    (T : CoefficientTensorModel f) {a b i j : ℕ}
    (x : hodgeCohomologyObject f a (i : ℤ))
    (y : hodgeCohomologyObject f b (j : ℤ)) :
    hodgeCohomologyObject f (a + b) ((i + j : ℕ) : ℤ) :=
  (eqToHom (congrArg (fun n : ℤ ↦ hodgeCohomologyObject f (a + b) n)
    (Nat.cast_add i j).symm)).hom
    ((@hodgeCupProduct X S f derivedMonoidal qhMonoidal.qh_monoidal globalLaxMonoidal
        T a b (i : ℤ) (j : ℤ)).hom
      (x ⊗ₜ[coefficientRing f] y))

/-- The elementwise Hodge cup product recovers the morphism-level Hodge cup product after
transporting along the canonical integer cast of the sum of degrees. -/
public theorem hodgeCup_eq_canonical (f : X ⟶ S)
    [derivedMonoidal : MonoidalCategory (coefficientDerived f)]
    [qhMonoidal : CoefficientQhMonoidal f]
    [globalLaxMonoidal : (globalDerivedFunctor f).LaxMonoidal]
    (T : CoefficientTensorModel f) {a b i j : ℕ}
    (x : hodgeCohomologyObject f a (i : ℤ))
    (y : hodgeCohomologyObject f b (j : ℤ)) :
    (eqToHom (congrArg (fun n : ℤ ↦ hodgeCohomologyObject f (a + b) n)
      (Nat.cast_add i j))).hom (hodgeCup f T x y) =
        (@hodgeCupProduct X S f derivedMonoidal qhMonoidal.qh_monoidal globalLaxMonoidal
          T a b (i : ℤ) (j : ℤ)).hom
          (x ⊗ₜ[coefficientRing f] y) := sorry

end AlgebraicGeometry.Scheme.DeRham
