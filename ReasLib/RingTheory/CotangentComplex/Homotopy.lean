/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Homotopy
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Diagonal homotopies of cotangent-complex maps

A diagonal factorization of a commutative square of ring maps makes the induced
scalar-extended map of cotangent complexes homotopic to zero.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace Algebra.CotangentComplex

/-- The ring-hom form of commutativity of a square of morphisms in `CommRingCat`. -/
theorem commSq_hom {A B A' B' : CommRingCat.{u}}
    {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
    (sq : CommSq ρ α β φ) :
    β.hom.comp ρ.hom = φ.hom.comp α.hom :=
  sorry

/-- A commutative square of ring maps with a diagonal making both triangles commute induces
a scalar-extended map of cotangent complexes homotopic to zero. -/
theorem map_homotopic_zero
    {A B A' B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
    (sq : CommSq ρ α β φ) (κ : B ⟶ A')
    (h_left : α ≫ κ = ρ) (h_right : κ ≫ β = φ) :
    Nonempty (Homotopy (map α.hom β.hom ρ.hom φ.hom (commSq_hom sq)) 0) :=
  sorry

end Algebra.CotangentComplex
