/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Regular.Basic
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Torsion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular multivariable linear forms

A finite family with injective coordinatewise multiplication determines a regular linear form in
the corresponding multivariable polynomial ring.

@stack 068P
-/

@[expose] public section

noncomputable section

universe u

open scoped BigOperators

namespace MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Lemma 15.30.16, tag `068P`: if coordinatewise multiplication by
`a : Fin n → R` is injective, then `∑ i, C (a i) * X i` is regular in
`MvPolynomial (Fin n) R`. -/
@[stacks 068P "a linear form with jointly faithful coefficients is regular"]
theorem isRegular_linearForm_of_smulFamilyMap_injective (a : Fin n → R)
    (h : Function.Injective (LocalizedModule.Away.Cech.smulFamilyMap R a)) :
    IsRegular (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) := sorry

/-- The principal-open localization formulation of regularity for a multivariable linear form. -/
@[stacks 068P "regular linear form from an injective principal-open family map"]
theorem isRegular_linearForm_of_awayFamilyMap_injective (a : Fin n → R)
    (h : Function.Injective (LocalizedModule.Away.Cech.familyMap R a)) :
    IsRegular (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) := sorry

end MvPolynomial
