/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence
public import ReasLib.CategoryTheory.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Right-Derived Exact Windows

For a fixed bounded-below right-derived model, maps of short exact complexes
induce maps between the direct `RⁿF` exact windows. Component formulas keep
downstream arguments independent of the implementation of `homMk₅`.
-/

open CategoryTheory.ComposableArrows
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.cohomological.exactWindow

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Naturality of the first map in one right-derived degree. -/
theorem map_f {S T : ShortComplex A} (φ : S ⟶ T) (n : ℕ) :
    (RightDerived.degree RF (n : ℤ)).map S.f ≫
        (RightDerived.degree RF (n : ℤ)).map φ.τ₂ =
      (RightDerived.degree RF (n : ℤ)).map φ.τ₁ ≫
        (RightDerived.degree RF (n : ℤ)).map T.f := sorry

/-- Naturality of the second map in one right-derived degree. -/
theorem map_g {S T : ShortComplex A} (φ : S ⟶ T) (n : ℕ) :
    (RightDerived.degree RF (n : ℤ)).map S.g ≫
        (RightDerived.degree RF (n : ℤ)).map φ.τ₃ =
      (RightDerived.degree RF (n : ℤ)).map φ.τ₂ ≫
        (RightDerived.degree RF (n : ℤ)).map T.g := sorry

/-- A map of short exact complexes induces a map between their direct
right-derived exact windows. -/
@[stacks 05TE "naturality map of right-derived exact windows"]
def map {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    RightDerived.cohomological.exactWindow RF hS n ⟶
      RightDerived.cohomological.exactWindow RF hT n :=
  ComposableArrows.homMk₅
    ((RightDerived.degree RF (n : ℤ)).map φ.τ₁)
    ((RightDerived.degree RF (n : ℤ)).map φ.τ₂)
    ((RightDerived.degree RF (n : ℤ)).map φ.τ₃)
    ((RightDerived.degree RF (n + 1 : ℕ)).map φ.τ₁)
    ((RightDerived.degree RF (n + 1 : ℕ)).map φ.τ₂)
    ((RightDerived.degree RF (n + 1 : ℕ)).map φ.τ₃)
    (map_f RF φ n) (map_g RF φ n)
    (connecting_naturality RF hS hT φ n).w.symm
    (map_f RF φ (n + 1)) (map_g RF φ (n + 1))

/-- The first component of the induced right-derived window map. -/
@[simp]
theorem map_app_zero {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (map RF hS hT φ n).app 0 =
      (RightDerived.degree RF (n : ℤ)).map φ.τ₁ := sorry

/-- The second component of the induced right-derived window map. -/
@[simp]
theorem map_app_one {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (map RF hS hT φ n).app 1 =
      (RightDerived.degree RF (n : ℤ)).map φ.τ₂ := sorry

/-- The third component of the induced right-derived window map. -/
@[simp]
theorem map_app_two {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (map RF hS hT φ n).app 2 =
      (RightDerived.degree RF (n : ℤ)).map φ.τ₃ := sorry

/-- The fourth component of the induced right-derived window map. -/
@[simp]
theorem map_app_three {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (map RF hS hT φ n).app 3 =
      (RightDerived.degree RF (n + 1 : ℕ)).map φ.τ₁ := sorry

/-- The fifth component of the induced right-derived window map. -/
@[simp]
theorem map_app_four {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (map RF hS hT φ n).app 4 =
      (RightDerived.degree RF (n + 1 : ℕ)).map φ.τ₂ := sorry

/-- The sixth component of the induced right-derived window map. -/
@[simp]
theorem map_app_five {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (map RF hS hT φ n).app 5 =
      (RightDerived.degree RF (n + 1 : ℕ)).map φ.τ₃ := sorry

/-- Identity maps of short exact complexes induce identity maps of direct
right-derived exact windows. -/
@[simp]
theorem map_id {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    map RF hS hS (𝟙 S) n =
      𝟙 (RightDerived.cohomological.exactWindow RF hS n) := sorry

/-- Direct right-derived exact-window maps preserve composition. -/
@[simp]
theorem map_comp {S T U : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (hU : U.ShortExact) (φ : S ⟶ T)
    (ψ : T ⟶ U) (n : ℕ) :
    map RF hS hU (φ ≫ ψ) n =
      map RF hS hT φ n ≫ map RF hT hU ψ n := sorry

end CategoryTheory.Functor.RightDerived.cohomological.exactWindow
