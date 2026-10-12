/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
public import ReasLib.RingTheory.Sequence.Koszul.Basic

/-!
# Finite-family Koszul complexes

This file presents the Koszul complex of a finite family through its canonical linear form on a
finite free module.

@stack 0623
@stack 0GZJ
-/

@[expose] public section

noncomputable section

universe u v

open Module

variable {R : Type u} [CommRing R]

/-- The linear form on the finite free module `ι → R` determined by a finite family `f`. -/
@[stacks 0623 "linear form associated to a finite family"]
abbrev koszulLinearForm {ι : Type v} [Finite ι] (f : ι → R) :
    (ι → R) →ₗ[R] R :=
  piEquiv ι R R f

/-- The finite-family linear form evaluates to the chosen coefficient on a standard basis vector.
The basis binder is explicit only where a finite coordinate model is actually used. -/
@[simp, stacks 0623 "finite-family linear form on a basis vector"]
theorem koszulLinearForm_basis {ι : Type v} [Fintype ι] (f : ι → R) (i : ι) :
    koszulLinearForm f (Pi.basisFun R ι i) = f i := sorry

namespace KoszulComplex

/-- The Koszul complex attached to a finite family of elements of a commutative ring.

This named declaration is the reusable owner of the finite-family construction.  The Unicode
notation below is only a short scoped view of this named API. -/
@[stacks 0623 "Koszul complex attached to a finite family"]
noncomputable abbrev family {ι : Type v} [Finite ι] (f : ι → R) :
    ChainComplex (ModuleCat R) ℕ :=
  koszulComplex (koszulLinearForm f)

/-- The degree `n` term of a finite-family Koszul complex is the corresponding exterior power. -/
@[simp, stacks 0623 "finite-family Koszul term"]
theorem family_X {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (family f).X n = (ModuleCat.of R (ι → R)).exteriorPower n := sorry

/-- Every term of a finite-family Koszul complex is free. -/
@[stacks 0623 "finite-family Koszul termwise free"]
theorem family_isTermwiseFree {ι : Type v} [Finite ι] (f : ι → R) :
    ChainComplex.IsTermwiseFree (family f) := sorry

/-- Every term of a finite-family Koszul complex is finite. -/
@[stacks 0623 "finite-family Koszul termwise finite"]
theorem family_isTermwiseFinite {ι : Type v} [Finite ι] (f : ι → R) :
    ChainComplex.IsTermwiseFinite (family f) := sorry

/-- The zero-based powered Koszul complex whose stage `n` uses the family `f i ^ (n + 1)`. -/
@[stacks 0623 "powered Koszul complex attached to a finite family",
  stacks 0GZJ "powered Koszul complex"]
noncomputable abbrev powerComplex {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  family fun i ↦ f i ^ (n + 1)

/-- Stable Unicode shorthand for the finite-family Koszul complex. -/
scoped notation:max "K•(" f ")" => family f

/-- Stable Unicode shorthand for the zero-based powered Koszul complex. -/
scoped notation:max "K•[" n "](" f ")" => powerComplex f n

end KoszulComplex
