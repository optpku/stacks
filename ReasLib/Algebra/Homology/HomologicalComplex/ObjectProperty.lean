/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Object Properties Defined Termwise on Homological Complexes

This file lifts an object property on a category to the corresponding
property of homological complexes whose terms all satisfy it.  The
construction is independent of chain/cochain orientation and of the index
type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type w} (c : ComplexShape I)

/-- The object property of homological complexes whose term in every degree
satisfies `P`. -/
def termsIn (P : ObjectProperty C) : ObjectProperty (HomologicalComplex C c) :=
  fun K => ∀ i : I, P (K.X i)

/-- Membership in `termsIn c P` is exactly the degreewise condition. -/
theorem mem_termsIn_iff (P : ObjectProperty C) (K : HomologicalComplex C c) :
    termsIn c P K ↔ ∀ i : I, P (K.X i) := sorry

/-- Homological complexes whose terms all satisfy `P`, as a full
subcategory. -/
abbrev TermsIn (P : ObjectProperty C) :=
  (termsIn c P).FullSubcategory

namespace TermsIn

variable {c} {P : ObjectProperty C}

/-- The canonical inclusion of termwise-`P` complexes into all homological
complexes of the same shape. -/
abbrev ι : TermsIn c P ⥤ HomologicalComplex C c :=
  ObjectProperty.ι _

/-- Every term of a complex in `TermsIn c P` satisfies `P`. -/
theorem term_mem (K : TermsIn c P) (i : I) : P (K.obj.X i) := sorry

end TermsIn

/-- A termwise object property is closed under isomorphisms when the original
object property is. -/
instance termsIn_isClosedUnderIsomorphisms
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (termsIn c P).IsClosedUnderIsomorphisms := sorry

end HomologicalComplex


namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type w} [AddRightCancelSemigroup I] [One I]

/-- The object property of chain complexes whose terms all satisfy `P`. -/
abbrev termsIn (P : ObjectProperty C) : ObjectProperty (ChainComplex C I) :=
  HomologicalComplex.termsIn (ComplexShape.down I) P

/-- Chain complexes whose terms all satisfy `P`, as a full subcategory. -/
abbrev TermsIn (I : Type w) [AddRightCancelSemigroup I] [One I]
    (P : ObjectProperty C) :=
  (termsIn (I := I) P).FullSubcategory

/-- Membership in `ChainComplex.termsIn P` is the degreewise condition. -/
theorem mem_termsIn_iff (P : ObjectProperty C) (K : ChainComplex C I) :
    termsIn P K ↔ ∀ i : I, P (K.X i) := sorry

namespace TermsIn

variable {P : ObjectProperty C}

/-- The canonical inclusion of termwise-`P` chain complexes. -/
abbrev ι : TermsIn I P ⥤ ChainComplex C I := ObjectProperty.ι _

/-- Every term of a chain complex in `TermsIn P` satisfies `P`. -/
theorem term_mem (K : TermsIn I P) (i : I) : P (K.obj.X i) := sorry

end TermsIn

end ChainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type w} [AddRightCancelSemigroup I] [One I]

/-- The object property of cochain complexes whose terms all satisfy `P`. -/
abbrev termsIn (P : ObjectProperty C) : ObjectProperty (CochainComplex C I) :=
  HomologicalComplex.termsIn (ComplexShape.up I) P

/-- Cochain complexes whose terms all satisfy `P`, as a full subcategory. -/
abbrev TermsIn (I : Type w) [AddRightCancelSemigroup I] [One I]
    (P : ObjectProperty C) :=
  (termsIn (I := I) P).FullSubcategory

/-- Membership in `CochainComplex.termsIn P` is the degreewise condition. -/
theorem mem_termsIn_iff (P : ObjectProperty C) (K : CochainComplex C I) :
    termsIn P K ↔ ∀ i : I, P (K.X i) := sorry

namespace TermsIn

variable {P : ObjectProperty C}

/-- The canonical inclusion of termwise-`P` cochain complexes. -/
abbrev ι : TermsIn I P ⥤ CochainComplex C I := ObjectProperty.ι _

/-- Every term of a cochain complex in `TermsIn P` satisfies `P`. -/
theorem term_mem (K : TermsIn I P) (i : I) : P (K.obj.X i) := sorry

end TermsIn

end CochainComplex

