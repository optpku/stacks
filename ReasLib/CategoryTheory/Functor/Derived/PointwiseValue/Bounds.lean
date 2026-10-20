/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomological Bounds for Pointwise Right-Derived Values

These statements retain only objectwise definedness.  In particular, they apply before a total
right-derived functor has been assembled.
-/

open CategoryTheory ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Value

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- Stacks 05TC (1): a pointwise right-derived value preserves a lower cohomological bound. -/
@[stacks 05TC]
theorem isGE
    (K : CochainComplex A ℤ) (a : ℤ) (hK : K.IsGE a)
    [(Functor.Homotopy.toDerived F).HasPointwiseRightDerivedFunctorAt
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj K)] :
    (CategoryTheory.Functor.RightDerived.Value.obj (Functor.Homotopy.toDerived F) (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj K)).IsGE a := sorry

namespace TruncLE

/-- Stacks 05TC (2): upper truncation induces an isomorphism on pointwise right-derived
cohomology in every retained degree. -/
@[stacks 05TC]
theorem homologyMap_isIso
    (K : CochainComplex A ℤ) (a i : ℤ) (hi : i ≤ a)
    [(Functor.Homotopy.toDerived F).HasPointwiseRightDerivedFunctorAt
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj K)]
    [(Functor.Homotopy.toDerived F).HasPointwiseRightDerivedFunctorAt
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj (K.truncLE a))] :
    IsIso
      ((DerivedCategory.homologyFunctor B i).map
        (CategoryTheory.Functor.RightDerived.Value.map (Functor.Homotopy.toDerived F) (HomotopyCategory.quasiIso A (up ℤ))
          ((HomotopyCategory.quotient A (up ℤ)).map (K.ιTruncLE a)))) := sorry

end TruncLE

end CategoryTheory.Functor.RightDerived.Value
