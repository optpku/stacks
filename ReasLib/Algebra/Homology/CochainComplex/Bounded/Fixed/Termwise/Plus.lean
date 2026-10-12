/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Plus
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting a Fixed Lower Bound

The fixed cutoff is useful construction data, but many consumers only need a bounded-below
termwise model. This file owns the canonical forgetful functors between those model categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex.StrictlyGE.TermsIn

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Regard a fixed-lower-bound termwise-`P` complex as a bounded-below complex. -/
@[stacks 05T6 "forgetting a fixed lower bound"]
def toPlus (P : ObjectProperty C) (a : ℤ) :
    StrictlyGE.TermsIn P a ⥤ Plus C :=
  (CochainComplex.plus C).lift
    (StrictlyGE.TermsIn.ι P a)
    (fun K ↦ ⟨a, K.property.1⟩)

/-- Forget the chosen lower cutoff while retaining the termwise object property. -/
@[stacks 05T6 "fixed-bound models as bounded-below termwise models"]
def forgetBound (P : ObjectProperty C) (a : ℤ) :
    StrictlyGE.TermsIn P a ⥤ Plus.TermsIn P :=
  ObjectProperty.lift (fun K : Plus C ↦ ∀ n : ℤ, P (K.obj.X n))
    (toPlus P a) (fun K n ↦ K.property.2 n)

/-- Forgetting the cutoff retains the underlying cochain complex. -/
@[simp]
theorem forgetBound_obj (P : ObjectProperty C) (a : ℤ)
    (K : StrictlyGE.TermsIn P a) :
    ((forgetBound P a).obj K : CochainComplex C ℤ) = K.obj := sorry

/-- Forgetting the cutoff retains the underlying cochain map. -/
@[simp]
theorem forgetBound_map (P : ObjectProperty C) (a : ℤ)
    {K L : StrictlyGE.TermsIn P a} (f : K ⟶ L) :
    (Plus.TermsIn.ι P).map ((forgetBound P a).map f) = f.hom := sorry

end CochainComplex.StrictlyGE.TermsIn


