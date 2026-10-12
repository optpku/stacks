/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.LeftDerived
import StacksCheckRecall

@[expose] public section

/-!
# Fiber homology computes derived projection lower shriek

The reusable construction and comparison API lives in
`ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar`.  This chapter file records the source
statement and its projective computational specialization.
-/

open CategoryTheory

/- Lemma 21.40.2 (08PJ): for a fibered category `X` over a Grothendieck site `J`, the universal
homological delta functor extending projection lower shriek has degree `n` canonically isomorphic
to the sheafification of degree-`n` fiber category homology. -/
@[stacks 08PJ "derived projection lower shriek as fiber homology"]
#check @FiberedCategoryOver.FiberHomology.Bar.universal_obj_isomorphic

@[stacks 08PJ "degree-zero projection lower shriek comparison"]
#check @FiberedCategoryOver.FiberHomology.Bar.lowerShriek_isomorphic_deltaFunctor_zero

@[stacks 08PJ "projective model for derived projection lower shriek"]
#check @FiberedCategoryOver.FiberHomology.Bar.leftDerived_obj_isomorphic

@[stacks 08PJ "universality of fiber homology"]
#check @FiberedCategoryOver.FiberHomology.Bar.deltaFunctor.isUniversal
