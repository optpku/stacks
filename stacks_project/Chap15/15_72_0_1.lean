/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import StacksCheckRecall

/-!
# Hom-complex cohomology and homotopy morphisms

Mathlib already owns the canonical equivalence from Hom-complex cohomology to shifted morphisms
in the homotopy category, so this equation is a direct recall.
-/

@[expose] public section

/-! # 15.72.0.1 (0A5X)

@stack 0A5X
-/

noncomputable section

universe u

open CochainComplex.HomComplex.CohomologyClass

variable {R : Type u} [Ring R]
variable (L M : CochainComplex (ModuleCat R) ℤ) (n : ℤ)

/- Equation 15.72.0.1: `H^n(Hom^•(L, M))` is the group of morphisms from `L` to the
`n`-shift of `M` in the homotopy category. -/
@[stacks 0A5X "Hom-complex cohomology and homotopy-category morphisms"]
#check (CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv
