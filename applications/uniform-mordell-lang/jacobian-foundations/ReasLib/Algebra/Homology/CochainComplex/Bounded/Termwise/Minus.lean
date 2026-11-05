module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Above Complexes with a Termwise Object Property

This file owns the category of bounded-above cochain complexes whose terms satisfy an arbitrary
object property. Replacement and resolution constructions should import this neutral model
category rather than own another copy of it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex.Minus

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The property that every term of a bounded-above cochain complex satisfies `P`. -/
@[stacks 05T7 "termwise object property on bounded-above complexes"]
def termsIn (P : ObjectProperty A) : ObjectProperty (Minus A) :=
  fun K ↦ ∀ n : ℤ, P (K.obj.X n)

/-- Membership in `Minus.termsIn P` means that every term satisfies `P`. -/
@[simp]
theorem mem_termsIn_iff (P : ObjectProperty A) (K : Minus A) :
    termsIn P K ↔ ∀ n : ℤ, P (K.obj.X n) := sorry

/-- A pointwise implication of object properties induces the corresponding implication on
bounded-above complexes. -/
theorem termsIn_mono {P Q : ObjectProperty A} (h : P ≤ Q) : termsIn P ≤ termsIn Q := sorry

/-- The bounded-above cochain complexes whose terms satisfy the object property `P`. -/
@[stacks 05T7 "bounded-above termwise-property complexes"]
abbrev TermsIn (P : ObjectProperty A) :=
  (termsIn P).FullSubcategory

namespace TermsIn

/-- A bounded-above termwise-`P` complex can be used as a bounded-above complex. -/
instance (P : ObjectProperty A) : CoeOut (TermsIn P) (Minus A) where
  coe K := K.obj

/-- A bounded-above termwise-`P` complex can be used as its underlying cochain complex. -/
instance (P : ObjectProperty A) : CoeOut (TermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- The inclusion of bounded-above termwise-`P` complexes into all cochain complexes. -/
abbrev ι (P : ObjectProperty A) : TermsIn P ⥤ CochainComplex A ℤ :=
  (termsIn P).ι ⋙ CochainComplex.Minus.ι A

/-- A bounded-above termwise-`P` complex is bounded above. -/
theorem minus {P : ObjectProperty A} (K : TermsIn P) :
    CochainComplex.minus A (K : CochainComplex A ℤ) := sorry

/-- Each term of a bounded-above termwise-`P` complex satisfies `P`. -/
theorem term_mem {P : ObjectProperty A} (K : TermsIn P) (n : ℤ) :
    P ((K : CochainComplex A ℤ).X n) := sorry

/-- A bounded-above termwise-`P` complex is zero in all sufficiently positive degrees. -/
theorem exists_bound {P : ObjectProperty A} (K : TermsIn P) :
    ∃ b : ℤ, (K : CochainComplex A ℤ).IsStrictlyLE b := sorry

end TermsIn

end CochainComplex.Minus


