/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Below Complexes with a Termwise Object Property

This file owns the category of bounded-below cochain complexes whose terms satisfy an arbitrary
object property. Replacement and resolution constructions should import this neutral model
category rather than own another copy of it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex.Plus

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The property that every term of a bounded-below cochain complex satisfies `P`. -/
@[stacks 05T6 "termwise object property on bounded-below complexes"]
def termsIn (P : ObjectProperty A) : ObjectProperty (Plus A) :=
  fun K ↦ ∀ n : ℤ, P (K.obj.X n)

/-- Membership in `Plus.termsIn P` means that every term satisfies `P`. -/
@[simp]
theorem mem_termsIn_iff (P : ObjectProperty A) (K : Plus A) :
    termsIn P K ↔ ∀ n : ℤ, P (K.obj.X n) := sorry

/-- A pointwise implication of object properties induces the corresponding implication on
bounded-below complexes. -/
theorem termsIn_mono {P Q : ObjectProperty A} (h : P ≤ Q) : termsIn P ≤ termsIn Q := sorry

/-- The bounded-below cochain complexes whose terms satisfy the object property `P`. -/
@[stacks 05T6 "bounded-below termwise-property complexes"]
abbrev TermsIn (P : ObjectProperty A) :=
  (termsIn P).FullSubcategory

namespace TermsIn

/-- A bounded-below termwise-`P` complex can be used as a bounded-below complex. -/
instance (P : ObjectProperty A) : CoeOut (TermsIn P) (Plus A) where
  coe K := K.obj

/-- A bounded-below termwise-`P` complex can be used as its underlying cochain complex. -/
instance (P : ObjectProperty A) : CoeOut (TermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- The inclusion of bounded-below termwise-`P` complexes into all cochain complexes. -/
abbrev ι (P : ObjectProperty A) : TermsIn P ⥤ CochainComplex A ℤ :=
  (termsIn P).ι ⋙ CochainComplex.Plus.ι A

/-- A bounded-below termwise-`P` complex is bounded below. -/
theorem plus {P : ObjectProperty A} (K : TermsIn P) :
    CochainComplex.plus A (K : CochainComplex A ℤ) := sorry

/-- Each term of a bounded-below termwise-`P` complex satisfies `P`. -/
theorem term_mem {P : ObjectProperty A} (K : TermsIn P) (n : ℤ) :
    P ((K : CochainComplex A ℤ).X n) := sorry

/-- A bounded-below termwise-`P` complex is zero in all sufficiently negative degrees. -/
theorem exists_bound {P : ObjectProperty A} (K : TermsIn P) :
    ∃ a : ℤ, (K : CochainComplex A ℤ).IsStrictlyGE a := sorry

end TermsIn

end CochainComplex.Plus


