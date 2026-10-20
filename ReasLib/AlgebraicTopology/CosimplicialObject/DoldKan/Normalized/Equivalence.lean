/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.MooreComparison

/-!
@stack 019I

# Cosimplicial Dold--Kan equivalence

The quotient-defined normalized cochain functor is identified with the transported normalized
Moore functor and thereby inherits its equivalence with nonnegative cochain complexes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace normalizedCochainComplex

/-- The quotient-defined normalized cochains realize the cosimplicial Dold--Kan equivalence
`CosimplicialObject A ≌ CochainComplex A ℕ`. -/
@[stacks 019I "cosimplicial Dold-Kan equivalence"]
def equivalence : CosimplicialObject A ≌ CochainComplex A ℕ :=
  (normalizedMooreCochainComplex.equivalence (A := A)).changeFunctor
    (comparison.natIso (A := A))

end normalizedCochainComplex

end CategoryTheory.CosimplicialObject
