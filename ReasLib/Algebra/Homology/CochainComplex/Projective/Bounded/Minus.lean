module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise.Minus
public import ReasLib.Algebra.Homology.CochainComplex.Projective.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting the lower bound of fixed-amplitude projective complexes

This leaf maps a projective complex supported in `[a, b]` to the canonical category of
bounded-above termwise-projective complexes.  It reuses the generic fixed-bound forgetful functor,
so projective resolutions do not need a second hand-built conversion.
@stack 0A5N
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex.ProjectiveIn

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- Fixed projective amplitude implies the fixed upper-bound termwise-projective property. -/
@[stacks 0A5N "fixed projective amplitude forgets to an upper bound"]
theorem le_strictlyLE_termsIn (a b : ℤ) :
    projectiveIn C a b ≤ StrictlyLE.termsIn (isProjective C) b := sorry

/-- Forget the lower cutoff while retaining bounded-above termwise projectivity. -/
@[stacks 0A5N "fixed projective amplitude as a bounded-above projective complex"]
def toProjectiveMinus (a b : ℤ) :
    ProjectiveIn C a b ⥤ Minus.TermsIn (isProjective C) :=
  (projectiveIn C a b).ιOfLE (le_strictlyLE_termsIn C a b) ⋙
    StrictlyLE.TermsIn.forgetBound (isProjective C) b

/-- Forgetting the lower cutoff retains the underlying cochain complex. -/
@[simp, stacks 0A5N "object of the projective-minus forgetful functor"]
theorem toProjectiveMinus_obj (a b : ℤ) (P : ProjectiveIn C a b) :
    ((toProjectiveMinus C a b).obj P : CochainComplex C ℤ) = P.obj := sorry

/-- Forgetting the lower cutoff retains the underlying cochain map. -/
@[simp, stacks 0A5N "map of the projective-minus forgetful functor"]
theorem toProjectiveMinus_map (a b : ℤ) {P Q : ProjectiveIn C a b} (f : P ⟶ Q) :
    (Minus.TermsIn.ι (isProjective C)).map ((toProjectiveMinus C a b).map f) = f.hom := sorry

end CochainComplex.ProjectiveIn
