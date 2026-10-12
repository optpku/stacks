/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Augmented
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Naturality
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp.Map
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Augmented Right-Derived Windows

Maps of short exact complexes induce maps of the standard low-degree
sequence written directly with `R⁰F` and `R¹F`.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open scoped CategoryTheory ZeroObject

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- A map of short exact complexes induces a map between their direct
augmented right-derived windows. -/
@[stacks 05TE "naturality map of augmented right-derived windows"]
def map {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    RightDerived.cohomological.augmentedWindow RF hS ⟶
      RightDerived.cohomological.augmentedWindow RF hT :=
  zeroPrecomp.map (exactWindow.map RF hS hT φ 0) 1

/-- Removing the initial zero component recovers the direct low-degree
exact-window naturality map. -/
@[simp]
theorem map_δ₀ {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    δ₀Functor.map (map RF hS hT φ) = exactWindow.map RF hS hT φ 0 := sorry

/-- The zero-object component of a direct augmented-window map is the
identity. -/
@[simp]
theorem map_app_zero {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    (map RF hS hT φ).app 0 = 𝟙 (0 : B) := sorry

/-- The `R⁰F(X₁)` component of a direct augmented-window map. -/
@[simp]
theorem map_app_one {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    (map RF hS hT φ).app 1 =
      (RightDerived.degree RF (0 : ℤ)).map φ.τ₁ := sorry

/-- The `R⁰F(X₂)` component of a direct augmented-window map. -/
@[simp]
theorem map_app_two {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    (map RF hS hT φ).app 2 =
      (RightDerived.degree RF (0 : ℤ)).map φ.τ₂ := sorry

/-- The `R⁰F(X₃)` component of a direct augmented-window map. -/
@[simp]
theorem map_app_three {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    (map RF hS hT φ).app 3 =
      (RightDerived.degree RF (0 : ℤ)).map φ.τ₃ := sorry

/-- The `R¹F(X₁)` component of a direct augmented-window map. -/
@[simp]
theorem map_app_four {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    (map RF hS hT φ).app 4 =
      (RightDerived.degree RF (1 : ℤ)).map φ.τ₁ := sorry

/-- The `R¹F(X₂)` component of a direct augmented-window map. -/
@[simp]
theorem map_app_five {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    (map RF hS hT φ).app 5 =
      (RightDerived.degree RF (1 : ℤ)).map φ.τ₂ := sorry

/-- The `R¹F(X₃)` component of a direct augmented-window map. -/
@[simp]
theorem map_app_six {S T : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) :
    (map RF hS hT φ).app 6 =
      (RightDerived.degree RF (1 : ℤ)).map φ.τ₃ := sorry

/-- Direct augmented-window maps preserve identities. -/
@[simp]
theorem map_id {S : ShortComplex A} (hS : S.ShortExact) :
    map RF hS hS (𝟙 S) =
      𝟙 (RightDerived.cohomological.augmentedWindow RF hS) := sorry

/-- Direct augmented-window maps preserve composition. -/
@[simp]
theorem map_comp {S T U : ShortComplex A} (hS : S.ShortExact)
    (hT : T.ShortExact) (hU : U.ShortExact) (φ : S ⟶ T)
    (ψ : T ⟶ U) :
    map RF hS hU (φ ≫ ψ) =
      map RF hS hT φ ≫ map RF hT hU ψ := sorry

end CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow
