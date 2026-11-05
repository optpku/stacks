/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Augmented
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Augmented Low-Degree Windows of Right Derived Functors

This leaf states the standard seven-object low-degree sequence directly in
terms of `R⁰F`, `R¹F`, and the explicit right-derived connecting morphism.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open scoped CategoryTheory
open scoped ZeroObject

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.cohomological

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- The direct low-degree right-derived window augmented on the left by the
zero object. -/
@[stacks 05TE "augmented low-degree right-derived exact window"]
def augmentedWindow
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [RF.CommShift ℤ] [RF.IsTriangulated]
    {S : ShortComplex A} (hS : S.ShortExact) : ComposableArrows B 6 :=
  (lowDegreeWindow RF hS).zeroPrecomp 1

/-- The augmented low-degree right-derived window is exact. -/
@[stacks 05TE "exactness of the augmented low-degree right-derived window"]
theorem augmentedWindow_exact
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [RF.CommShift ℤ] [RF.IsTriangulated]
    {S : ShortComplex A} (hS : S.ShortExact)
    (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] :
    (augmentedWindow RF hS).Exact := sorry

namespace augmentedWindow

variable (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Removing the initial zero morphism recovers the direct low-degree
right-derived window. -/
@[simp]
theorem δ₀ {S : ShortComplex A} (hS : S.ShortExact) :
    (augmentedWindow RF hS).δ₀ = lowDegreeWindow RF hS := sorry

/-- The first arrow of the direct augmented window is zero. -/
@[simp]
theorem map_zero_one {S : ShortComplex A} (hS : S.ShortExact) :
    (augmentedWindow RF hS).map' 0 1 =
      (0 : (0 : B) ⟶ (RightDerived.degree RF (0 : ℤ)).obj S.X₁) := sorry

/-- The next arrow is the degree-zero right-derived image of the first map. -/
@[simp]
theorem map_f_zero {S : ShortComplex A} (hS : S.ShortExact) :
    (augmentedWindow RF hS).map' 1 2 =
      (RightDerived.degree RF (0 : ℤ)).map S.f := sorry

/-- The third arrow is the degree-zero right-derived image of the second map. -/
@[simp]
theorem map_g_zero {S : ShortComplex A} (hS : S.ShortExact) :
    (augmentedWindow RF hS).map' 2 3 =
      (RightDerived.degree RF (0 : ℤ)).map S.g := sorry

/-- The middle arrow is the direct degree-zero right-derived connecting map. -/
@[simp]
theorem connecting_zero {S : ShortComplex A} (hS : S.ShortExact) :
    (augmentedWindow RF hS).map' 3 4 = connecting RF hS 0 := sorry

/-- The fifth arrow is the degree-one right-derived image of the first map. -/
@[simp]
theorem map_f_one {S : ShortComplex A} (hS : S.ShortExact) :
    (augmentedWindow RF hS).map' 4 5 =
      (RightDerived.degree RF (1 : ℤ)).map S.f := sorry

/-- The last arrow is the degree-one right-derived image of the second map. -/
@[simp]
theorem map_g_one {S : ShortComplex A} (hS : S.ShortExact) :
    (augmentedWindow RF hS).map' 5 6 =
      (RightDerived.degree RF (1 : ℤ)).map S.g := sorry

end augmentedWindow

end CategoryTheory.Functor.RightDerived.cohomological
