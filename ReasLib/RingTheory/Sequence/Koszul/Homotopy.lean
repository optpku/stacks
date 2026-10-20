/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import ReasLib.RingTheory.Sequence.Koszul.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul contraction homotopies

This file owns the canonical left-wedge homotopy showing that multiplication by the value of a
linear form is null-homotopic on its Koszul complex.

@stack 0626
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace KoszulComplex

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

/-- The degreewise left-wedge components of the canonical Koszul contraction homotopy. -/
@[stacks 0626 "components of the Koszul contraction homotopy"]
noncomputable abbrev leftWedgeHomotopyComponent (φ : E →ₗ[R] R) (e : E) :
    ∀ i j, (ComplexShape.down ℕ).Rel j i → ((koszulComplex φ).X i ⟶ (koszulComplex φ).X j)
  | i, _, h => h ▸ leftWedge e i

/-- A left-wedge homotopy component is the canonical categorical left-wedge morphism. -/
@[simp]
theorem leftWedgeHomotopyComponent_apply (φ : E →ₗ[R] R) (e : E) (n : ℕ) :
    leftWedgeHomotopyComponent φ e n (n + 1) (ComplexShape.down_mk (n + 1) n rfl) =
      leftWedge e n := sorry

/-- The canonical null-homotopy whose underlying map is built from left wedge. -/
@[stacks 0626 "left-wedge null-homotopy"]
noncomputable abbrev leftWedgeNullHomotopy (φ : E →ₗ[R] R) (e : E) :
    Homotopy (Homotopy.nullHomotopicMap' (leftWedgeHomotopyComponent φ e)) 0 :=
  Homotopy.nullHomotopy' (leftWedgeHomotopyComponent φ e)

/-- Multiplication by `φ e` is the endomorphism induced by the canonical left-wedge homotopy. -/
@[stacks 0626 "scalar multiplication on a Koszul complex is null-homotopic"]
theorem smulId_eq_nullHomotopicMap (φ : E →ₗ[R] R) (e : E) :
    (φ e) • 𝟙 (koszulComplex φ) =
      Homotopy.nullHomotopicMap' (leftWedgeHomotopyComponent φ e) := sorry

/-- Multiplication by `φ e` on the Koszul complex of `φ` is canonically homotopic to zero. -/
@[stacks 0626 "canonical Koszul scalar null-homotopy"]
noncomputable def scalarHomotopyZero (φ : E →ₗ[R] R) (e : E) :
    Homotopy ((φ e) • 𝟙 (koszulComplex φ)) 0 :=
  (Homotopy.ofEq (smulId_eq_nullHomotopicMap φ e)).trans (leftWedgeNullHomotopy φ e)

end KoszulComplex
