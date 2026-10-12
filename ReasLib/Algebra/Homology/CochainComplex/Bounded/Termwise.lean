/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Plus
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Plus.Localization
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus.Localization
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty

/-!
# Bounded complexes with a termwise object property

This file combines the independent notions of boundedness and termwise membership in an object
property.  It is the reusable owner for constructions such as strictly perfect complexes, rather
than a specialization to module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The object property of bounded cochain complexes whose terms satisfy `P`. -/
def boundedTermsIn (P : ObjectProperty C) : ObjectProperty (CochainComplex C ℤ) :=
  CochainComplex.bounded C ⊓ CochainComplex.termsIn P

/-- Membership in `boundedTermsIn P` is boundedness together with termwise membership in `P`. -/
theorem mem_boundedTermsIn_iff (P : ObjectProperty C) (K : CochainComplex C ℤ) :
    boundedTermsIn P K ↔ CochainComplex.bounded C K ∧ ∀ i : ℤ, P (K.X i) := sorry

/-- Bounded cochain complexes whose terms satisfy `P`, as a full subcategory. -/
abbrev BoundedTermsIn (P : ObjectProperty C) :=
  (boundedTermsIn P).FullSubcategory

namespace BoundedTermsIn

variable {P : ObjectProperty C}

/-- The canonical inclusion of bounded termwise-`P` complexes. -/
abbrev ι : BoundedTermsIn P ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι _

/-- A complex in `BoundedTermsIn P` is bounded. -/
theorem bounded (K : BoundedTermsIn P) : CochainComplex.bounded C K.obj := sorry

/-- Every term of a complex in `BoundedTermsIn P` satisfies `P`. -/
theorem term_mem (K : BoundedTermsIn P) (i : ℤ) : P (K.obj.X i) := sorry

end BoundedTermsIn

end CochainComplex
