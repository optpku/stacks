/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap110.«110_64_0_1_Columns»

/-!
# The dual-number endomorphism diagram in the homotopy category
-/

@[expose] public section

open scoped DualNumber
open CategoryTheory HomologicalComplex HomotopyCategory ComplexShape
open CochainComplex.DualNumber

universe u

namespace CochainComplex.DualNumber

variable (k : Type u) [Field k]

/-- 110.64.0.1: over a field `k`, with `R = k[ε]`, the displayed endomorphism
diagram on the columns `columnA k`, `columnB k`, `columnC k` commutes in the
homotopy category `K(k[ε])`. The left square, with vertical maps `1+ε` and `1`,
commutes up to the homotopy `1 : A^1 ⟶ B^0`. -/
@[stacks 087K]
theorem leftSquare_commutes_up_to_homotopy :
    (quotient (ModuleCat (k[ε])) (up ℤ)).map (oneAddEps k ≫ toB k) =
      (quotient (ModuleCat (k[ε])) (up ℤ)).map (toB k) :=
  sorry

/-- The right square of the displayed diagram, with vertical identities on
`columnB` and `columnC`, commutes strictly. -/
theorem rightSquare_commutes :
    𝟙 (columnB k) ≫ toC k = toC k ≫ 𝟙 (columnC k) :=
  sorry

end CochainComplex.DualNumber
