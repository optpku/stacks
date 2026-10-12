/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Transport of valuative commutative squares

This module transports a valuative commutative square along a commutative square of scheme
morphisms and records the valuative square induced by a chosen lift of the transported square.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ValuativeCommSq

/-- Transport a valuative commutative square along a commutative square of scheme morphisms. -/
noncomputable def map {X₁ Y₁ X₂ Y₂ : Scheme.{u}} {f₁ : X₁ ⟶ Y₁}
    (sq : ValuativeCommSq f₁) {g : X₁ ⟶ X₂} {h : Y₁ ⟶ Y₂} {f₂ : X₂ ⟶ Y₂}
    (w : CommSq f₁ g h f₂) : ValuativeCommSq f₂ where
  R := sq.R
  commRing := sq.commRing
  domain := sq.domain
  valuationRing := sq.valuationRing
  K := sq.K
  field := sq.field
  algebra := sq.algebra
  isFractionRing := sq.isFractionRing
  i₁ := sq.i₁ ≫ g
  i₂ := sq.i₂ ≫ h
  commSq := ⟨by rw [Category.assoc, ← w.w, ← Category.assoc, sq.commSq.w, Category.assoc]⟩

/-- A lift of a transported valuative square induces a valuative square over the left-hand
morphism. -/
noncomputable def leftOfMapLift {X₁ Y₁ X₂ Y₂ : Scheme.{u}} {f₁ : X₁ ⟶ Y₁}
    (sq : ValuativeCommSq f₁) {g : X₁ ⟶ X₂} {h : Y₁ ⟶ Y₂} {f₂ : X₂ ⟶ Y₂}
    (w : CommSq f₁ g h f₂) (l : (sq.map w).commSq.LiftStruct) : ValuativeCommSq g where
  R := sq.R
  commRing := sq.commRing
  domain := sq.domain
  valuationRing := sq.valuationRing
  K := sq.K
  field := sq.field
  algebra := sq.algebra
  isFractionRing := sq.isFractionRing
  i₁ := sq.i₁
  i₂ := l.l
  commSq := ⟨l.fac_left.symm⟩

end AlgebraicGeometry.ValuativeCommSq
