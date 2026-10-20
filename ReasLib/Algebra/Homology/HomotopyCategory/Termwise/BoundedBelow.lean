/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Termwise Bounded-Below Homotopy Categories

This leaf is independent of a choice of injective, projective, flat, or other
termwise property. It turns an `ObjectProperty` on an abelian category into
the corresponding full subcategory of its bounded-below homotopy category and
provides the quotient bridge from bounded-below cochain complexes.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

namespace HomotopyCategory.Plus

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- The bounded-below homotopy objects whose representing cochain complexes
have all terms in `P`. -/
@[stacks 013W]
def termsIn (P : ObjectProperty 𝒜) : ObjectProperty (HomotopyCategory.Plus 𝒜) :=
  fun K ↦ ∀ n : ℤ, P (K.obj.as.X n)

/-- The full subcategory of bounded-below homotopy objects whose terms lie in
the object property `P`. -/
@[stacks 013W]
abbrev TermsIn (P : ObjectProperty 𝒜) :=
  (termsIn 𝒜 P).FullSubcategory

namespace TermsIn

variable {P : ObjectProperty 𝒜}

/-- The canonical inclusion of a termwise-defined bounded-below homotopy
subcategory into the bounded-below homotopy category. -/
abbrev ι : TermsIn 𝒜 P ⥤ HomotopyCategory.Plus 𝒜 :=
  (termsIn 𝒜 P).ι

/-- The canonical inclusion of a termwise-defined bounded-below homotopy
subcategory is fully faithful. -/
abbrev fullyFaithfulι : (ι 𝒜 (P := P)).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Every term of an object of `TermsIn P` belongs to `P`. -/
theorem term_mem (I : TermsIn 𝒜 P) (n : ℤ) :
    P (I.obj.obj.as.X n) := sorry

/-- The underlying cochain complex of an object of `TermsIn P` is bounded
below. -/
theorem plus (I : TermsIn 𝒜 P) :
    CochainComplex.plus 𝒜 I.obj.obj.as := sorry

/-- An object of the termwise homotopy subcategory, viewed as its underlying
bounded-below cochain complex together with its termwise property. -/
@[stacks 013W]
noncomputable def toCochain (I : TermsIn 𝒜 P) :
    CochainComplex.Plus.TermsIn P :=
  ⟨⟨I.obj.obj.as, plus 𝒜 I⟩, fun n ↦ term_mem 𝒜 I n⟩

end TermsIn

end HomotopyCategory.Plus

end CategoryTheory

namespace CochainComplex

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

namespace Plus.TermsIn

/-- The bounded-below homotopy quotient sends a bounded-below complex whose
terms satisfy `P` to an object of the corresponding termwise homotopy
subcategory. -/
theorem quotient_mem_termsIn (P : ObjectProperty 𝒜) (I : Plus.TermsIn P) :
    HomotopyCategory.Plus.termsIn 𝒜 P
      ((ObjectProperty.ι
        (fun K : Plus 𝒜 ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
          HomotopyCategory.Plus.quotient 𝒜).obj I) := sorry

/-- The quotient bridge from bounded-below cochain complexes with terms in
`P` to the corresponding termwise homotopy subcategory. -/
@[stacks 013W]
noncomputable def toHomotopy (P : ObjectProperty 𝒜) :
    Plus.TermsIn P ⥤ HomotopyCategory.Plus.TermsIn 𝒜 P :=
  (HomotopyCategory.Plus.termsIn 𝒜 P).lift
    (ObjectProperty.ι
      (fun K : Plus 𝒜 ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
        HomotopyCategory.Plus.quotient 𝒜)
    (quotient_mem_termsIn 𝒜 P)

/-- Forgetting the termwise property after `toHomotopy` recovers the canonical
bounded-below homotopy quotient functor. -/
@[stacks 013W]
noncomputable def toHomotopyCompιIso (P : ObjectProperty 𝒜) :
    toHomotopy 𝒜 P ⋙ HomotopyCategory.Plus.TermsIn.ι 𝒜 ≅
      ObjectProperty.ι
        (fun K : Plus 𝒜 ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
          HomotopyCategory.Plus.quotient 𝒜 :=
  ObjectProperty.liftCompιIso
    (HomotopyCategory.Plus.termsIn 𝒜 P)
    (ObjectProperty.ι
      (fun K : Plus 𝒜 ↦ ∀ n : ℤ, P (K.obj.X n)) ⋙
        HomotopyCategory.Plus.quotient 𝒜)
    (quotient_mem_termsIn 𝒜 P)

end Plus.TermsIn

end CochainComplex


