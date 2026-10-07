module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting a Fixed Upper Bound

The fixed cutoff is useful construction data, but many consumers only need a bounded-above
termwise model. This file owns the canonical forgetful functors between those model categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex.StrictlyLE.TermsIn

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Regard a fixed-upper-bound termwise-`P` complex as a bounded-above complex. -/
@[stacks 05T7 "forgetting a fixed upper bound"]
def toMinus (P : ObjectProperty C) (a : ℤ) :
    StrictlyLE.TermsIn P a ⥤ Minus C :=
  (CochainComplex.minus C).lift
    (StrictlyLE.TermsIn.ι P a)
    (fun K ↦ ⟨a, K.property.1⟩)

/-- Forget the chosen upper cutoff while retaining the termwise object property. -/
@[stacks 05T7 "fixed-bound models as bounded-above termwise models"]
def forgetBound (P : ObjectProperty C) (a : ℤ) :
    StrictlyLE.TermsIn P a ⥤ Minus.TermsIn P :=
  ObjectProperty.lift (fun K : Minus C ↦ ∀ n : ℤ, P (K.obj.X n))
    (toMinus P a) (fun K n ↦ K.property.2 n)

/-- Forgetting the cutoff retains the underlying cochain complex. -/
@[simp]
theorem forgetBound_obj (P : ObjectProperty C) (a : ℤ)
    (K : StrictlyLE.TermsIn P a) :
    ((forgetBound P a).obj K : CochainComplex C ℤ) = K.obj := sorry

/-- Forgetting the cutoff retains the underlying cochain map. -/
@[simp]
theorem forgetBound_map (P : ObjectProperty C) (a : ℤ)
    {K L : StrictlyLE.TermsIn P a} (f : K ⟶ L) :
    (Minus.TermsIn.ι P).map ((forgetBound P a).map f) = f.hom := sorry

end CochainComplex.StrictlyLE.TermsIn


