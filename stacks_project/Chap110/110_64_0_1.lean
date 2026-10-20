/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DualNumber
import StacksCheckRecall

/-!
# The dual-number endomorphism diagram in the homotopy category
-/

@[expose] public section

open scoped DualNumber
open CategoryTheory HomologicalComplex HomotopyCategory ComplexShape
open CochainComplex.DualNumber

universe u

/- 110.64.0.1: over a field `k`, with `R = k[ε]`, the displayed endomorphism
diagram on the columns `columnA k`, `columnB k`, `columnC k` commutes in the
homotopy category `K(k[ε])`. The left square, with vertical maps `1+ε` and `1`,
commutes up to the homotopy `1 : A^1 ⟶ B^0`; the right square commutes strictly. -/
@[stacks 087K] #check (CochainComplex.DualNumber.diagram_commutes :
  ∀ (k : Type u) [Field k],
    ((quotient (ModuleCat (k[ε])) (up ℤ)).map (oneAddEps k ≫ toB k) =
      (quotient (ModuleCat (k[ε])) (up ℤ)).map (toB k)) ∧
      (𝟙 (columnB k) ≫ toC k = toC k ≫ 𝟙 (columnC k)))
