/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Termwise Bounded-Above Homotopy Categories

This leaf turns an object property on an abelian category into the corresponding full
subcategory of its bounded-above homotopy category.  It is the formal dual of the bounded-below
termwise owner and provides the quotient bridge from bounded-above cochain complexes.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

namespace HomotopyCategory.Minus

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The bounded-above homotopy objects whose representing cochain complexes have all terms in
`P`. -/
def termsIn (P : ObjectProperty A) : ObjectProperty (HomotopyCategory.Minus A) :=
  fun K ↦ ∀ n : ℤ, P (K.obj.as.X n)

/-- The full subcategory of bounded-above homotopy objects whose terms lie in `P`. -/
abbrev TermsIn (P : ObjectProperty A) :=
  (termsIn A P).FullSubcategory

namespace TermsIn

variable {P : ObjectProperty A}

/-- The canonical inclusion of a termwise-defined bounded-above homotopy subcategory. -/
abbrev ι : TermsIn A P ⥤ HomotopyCategory.Minus A :=
  (termsIn A P).ι

/-- The termwise bounded-above inclusion is fully faithful. -/
abbrev fullyFaithfulι : (ι A (P := P)).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Every term of an object of `TermsIn P` belongs to `P`. -/
theorem term_mem (I : TermsIn A P) (n : ℤ) :
    P (I.obj.obj.as.X n) := sorry

/-- The underlying cochain complex of an object of `TermsIn P` is bounded above. -/
theorem minus (I : TermsIn A P) :
    CochainComplex.minus A I.obj.obj.as := sorry

/-- An object of the termwise homotopy subcategory, viewed as a bounded-above cochain complex
together with its termwise property. -/
noncomputable def toCochain (I : TermsIn A P) :
    CochainComplex.Minus.TermsIn P :=
  ⟨⟨I.obj.obj.as, minus A I⟩, fun n ↦ term_mem A I n⟩

end TermsIn

end HomotopyCategory.Minus

end CategoryTheory

namespace CochainComplex

variable (A : Type u) [Category.{v} A] [Abelian A]

namespace Minus.TermsIn

/-- The bounded-above homotopy quotient sends a bounded-above complex whose terms satisfy `P`
to the corresponding termwise homotopy subcategory. -/
theorem quotient_mem_termsIn (P : ObjectProperty A) (I : Minus.TermsIn P) :
    HomotopyCategory.Minus.termsIn A P
      ((ObjectProperty.ι
        (fun K : Minus A ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
          HomotopyCategory.Minus.quotient A).obj I) := sorry

/-- The quotient bridge from bounded-above cochain complexes with terms in `P` to the
corresponding termwise homotopy subcategory. -/
noncomputable def toHomotopy (P : ObjectProperty A) :
    Minus.TermsIn P ⥤ HomotopyCategory.Minus.TermsIn A P :=
  (HomotopyCategory.Minus.termsIn A P).lift
    (ObjectProperty.ι
      (fun K : Minus A ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
        HomotopyCategory.Minus.quotient A)
    (quotient_mem_termsIn A P)

/-- Forgetting the termwise property after `toHomotopy` recovers the bounded-above homotopy
quotient functor. -/
noncomputable def toHomotopyCompιIso (P : ObjectProperty A) :
    toHomotopy A P ⋙ HomotopyCategory.Minus.TermsIn.ι A ≅
      ObjectProperty.ι
        (fun K : Minus A ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
          HomotopyCategory.Minus.quotient A :=
  ObjectProperty.liftCompιIso
    (HomotopyCategory.Minus.termsIn A P)
    (ObjectProperty.ι
      (fun K : Minus A ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
        HomotopyCategory.Minus.quotient A)
    (quotient_mem_termsIn A P)

end Minus.TermsIn

end CochainComplex


