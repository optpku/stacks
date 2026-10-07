module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Homology
import StacksCheckRecall

/-!
# Lemma 15.75.7

@stack 066U

The source bounded object is Mathlib's canonical `DerivedCategory.Bounded` object, and its
cohomology is read through the restricted bounded-derived cohomology functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

variable (R : Type u) [Ring R]

/- Lemma 15.75.7 (066U): perfect cohomology of a bounded object implies perfectness. -/
@[stacks 066U "bounded object with perfect cohomology"]
#check
  (DerivedCategory.IsPerfect.of_bounded_of_homology :
    (K : DerivedCategory.Bounded (ModuleCat R)) →
      (∀ i : ℤ,
        ((DerivedCategory.Bounded.homologyFunctor (ModuleCat R) i).obj K).IsPerfect) →
      K.obj.IsPerfect)

#check @ModuleCat.IsPerfect
