/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import ReasLib.RingTheory.MvPolynomial.LinearForm
public import ReasLib.RingTheory.Sequence.Koszul.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal upper-triangular changes of a finite family

The universal upper-triangular coefficient matrix has invertible diagonal entries.  It gives a
faithfully flat smooth base change on which a proper Koszul-regular family becomes regular.

@stack 068Q
-/

@[expose] public section

noncomputable section

universe u

open MvPolynomial

namespace RingTheory.Sequence.UpperTriangular

/-- The pairs `(i, j)` with `i ≤ j` indexing an upper-triangular matrix. -/
@[stacks 068Q "upper-triangular matrix indices"]
abbrev Index (n : ℕ) := { ij : Fin n × Fin n // ij.1 ≤ ij.2 }

/-- The polynomial algebra in the upper-triangular entries, localized at the product of the
diagonal variables. -/
@[stacks 068Q "universal upper-triangular base-change ring"]
abbrev Ring (R : Type u) [CommRing R] (n : ℕ) :=
  Localization.Away
    (∏ i : Fin n, (X ⟨(i, i), le_rfl⟩ : MvPolynomial (Index n) R))

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Lemma 15.30.17 (1), tag `068Q`: the universal
upper-triangular base-change ring is faithfully flat over the coefficient ring. -/
@[stacks 068Q "Lemma 15.30.17 (1)"]
instance faithfullyFlat : Module.FaithfullyFlat R (Ring R n) := sorry

/-- Lemma 15.30.17 (2), tag `068Q`: the universal
upper-triangular base-change ring is smooth over the coefficient ring. -/
@[stacks 068Q "Lemma 15.30.17 (2)"]
instance smooth : Algebra.Smooth R (Ring R n) := sorry

/-- The universal upper-triangular matrix over `Ring R n`. -/
@[stacks 068Q "universal upper-triangular matrix"]
noncomputable def matrix : Matrix (Fin n) (Fin n) (Ring R n) :=
  Matrix.of fun i j ↦
    if hij : i ≤ j then
      algebraMap (MvPolynomial (Index n) R) (Ring R n) (X ⟨(i, j), hij⟩)
    else 0

/-- The universal matrix entry is its upper-triangular variable when `i ≤ j`, and zero below
the diagonal. -/
@[stacks 068Q "universal upper-triangular matrix application"]
theorem matrix_apply (i j : Fin n) :
    matrix (R := R) (n := n) i j =
      if hij : i ≤ j then
        algebraMap (MvPolynomial (Index n) R) (Ring R n) (X ⟨(i, j), hij⟩)
      else 0 := sorry

/-- The family obtained by multiplying `f` by the universal upper-triangular matrix. -/
@[stacks 068Q "universal upper-triangular family"]
noncomputable def family (f : Fin n → R) : Fin n → Ring R n :=
  Matrix.mulVec (matrix (R := R) (n := n))
    (fun j ↦ algebraMap R (Ring R n) (f j))

/-- The `i`-th universal upper-triangular combination is the sum over entries with `i ≤ j`. -/
@[stacks 068Q "universal upper-triangular family application"]
theorem family_apply (f : Fin n → R) (i : Fin n) :
    family f i =
      ∑ j, if hij : i ≤ j then
        algebraMap (MvPolynomial (Index n) R) (Ring R n) (X ⟨(i, j), hij⟩) *
          algebraMap R (Ring R n) (f j)
      else 0 := sorry

/-- Universal upper-triangular change of generators preserves the generated ideal after base
change. -/
@[stacks 068Q "upper-triangular change preserves the generated ideal"]
theorem map_span_eq_span (f : Fin n → R) :
    Ideal.map (algebraMap R (Ring R n)) (Ideal.span (Set.range f)) =
      Ideal.span (Set.range (family f)) := sorry

end RingTheory.Sequence.UpperTriangular

namespace RingTheory.Sequence.IsKoszulRegularSequence

open UpperTriangular

variable {R : Type u} [CommRing R] {n : ℕ} {f : Fin n → R}

/-- Lemma 15.30.17 (3), tag `068Q`: after the universal
upper-triangular faithfully flat smooth base change, a proper Koszul-regular family is regular. -/
@[stacks 068Q "Lemma 15.30.17 (3)"]
theorem isRegular_upperTriangular (h : IsKoszulRegularSequence f)
    (hproper : Ideal.span (Set.range f) ≠ (⊤ : Ideal R)) :
    IsRegular (UpperTriangular.Ring R n) (List.ofFn (UpperTriangular.family f)) := sorry

end RingTheory.Sequence.IsKoszulRegularSequence
