/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed Bounds with a Termwise Object Property

This file intersects a fixed strict bound with a termwise object property.  Keeping the bound in
the object-property owner lets resolution data retain its precise cutoff without adding a
separate proof field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace StrictlyGE

/-- The object property of complexes strictly bounded below at `a` whose terms satisfy `P`. -/
@[stacks 05T6 "fixed lower bound with a termwise object property"]
def termsIn (P : ObjectProperty C) (a : ℤ) : ObjectProperty (CochainComplex C ℤ) :=
  CochainComplex.strictlyGE C a ⊓ CochainComplex.termsIn P

/-- Membership in `StrictlyGE.termsIn P a` is the fixed lower bound together with termwise
membership in `P`. -/
@[stacks 05T6 "membership in fixed-lower-bound termwise complexes"]
theorem mem_termsIn_iff (P : ObjectProperty C) (a : ℤ) (K : CochainComplex C ℤ) :
    termsIn P a K ↔ K.IsStrictlyGE a ∧ ∀ i : ℤ, P (K.X i) := sorry

/-- Complexes strictly bounded below at `a` whose terms satisfy `P`. -/
@[stacks 05T6 "fixed-lower-bound termwise complexes"]
abbrev TermsIn (P : ObjectProperty C) (a : ℤ) :=
  (termsIn P a).FullSubcategory

namespace TermsIn

variable {P : ObjectProperty C} {a : ℤ}

/-- The inclusion of fixed-lower-bound termwise complexes into all cochain complexes. -/
abbrev ι (P : ObjectProperty C) (a : ℤ) :
    StrictlyGE.TermsIn P a ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι _

/-- The underlying complex retains its fixed strict lower bound. -/
instance isStrictlyGE (K : StrictlyGE.TermsIn P a) : K.obj.IsStrictlyGE a := sorry

/-- Every term of a fixed-lower-bound termwise complex satisfies `P`. -/
theorem term_mem (K : StrictlyGE.TermsIn P a) (i : ℤ) : P (K.obj.X i) := sorry

end TermsIn

end StrictlyGE

namespace StrictlyLE

/-- The object property of complexes strictly bounded above at `a` whose terms satisfy `P`. -/
@[stacks 05T7 "fixed upper bound with a termwise object property"]
def termsIn (P : ObjectProperty C) (a : ℤ) : ObjectProperty (CochainComplex C ℤ) :=
  CochainComplex.strictlyLE C a ⊓ CochainComplex.termsIn P

/-- Membership in `StrictlyLE.termsIn P a` is the fixed upper bound together with termwise
membership in `P`. -/
@[stacks 05T7 "membership in fixed-upper-bound termwise complexes"]
theorem mem_termsIn_iff (P : ObjectProperty C) (a : ℤ) (K : CochainComplex C ℤ) :
    termsIn P a K ↔ K.IsStrictlyLE a ∧ ∀ i : ℤ, P (K.X i) := sorry

/-- Complexes strictly bounded above at `a` whose terms satisfy `P`. -/
@[stacks 05T7 "fixed-upper-bound termwise complexes"]
abbrev TermsIn (P : ObjectProperty C) (a : ℤ) :=
  (termsIn P a).FullSubcategory

namespace TermsIn

variable {P : ObjectProperty C} {a : ℤ}

/-- The inclusion of fixed-upper-bound termwise complexes into all cochain complexes. -/
abbrev ι (P : ObjectProperty C) (a : ℤ) :
    StrictlyLE.TermsIn P a ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι _

/-- The underlying complex retains its fixed strict upper bound. -/
instance isStrictlyLE (K : StrictlyLE.TermsIn P a) : K.obj.IsStrictlyLE a := sorry

/-- Every term of a fixed-upper-bound termwise complex satisfies `P`. -/
theorem term_mem (K : StrictlyLE.TermsIn P a) (i : ℤ) : P (K.obj.X i) := sorry

end TermsIn

end StrictlyLE

end CochainComplex


