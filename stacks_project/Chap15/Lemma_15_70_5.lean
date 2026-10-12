/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Bounded
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.70.5: finite injective dimension from bounded data

The two conclusions are owned at the level of an arbitrary abelian category with enough
injectives.  In the module-category specialization, bounded cohomology is read through
`DerivedCategory.Bounded.homologyFunctor`, and a bounded representative is carried by
`CochainComplex.Bounded`.

@stack 0A5V
-/

/- Lemma 15.70.5 (1), tag `0A5V`: bounded cohomology objects of finite injective dimension give
finite injective dimension of the derived object. -/
@[stacks 0A5V "(1), bounded cohomology"]
#check @CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension.ofBoundedHomology

/- Lemma 15.70.5 (2), tag `0A5V`: an arbitrary derived object represented by a bounded complex
with termwise finite injective dimension has finite injective dimension. -/
@[stacks 0A5V "(2), bounded representative"]
#check @CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension.ofBoundedRepresentative

/- The direct `Q.obj` specialization remains available when no transport is needed. -/
#check @CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension.ofBoundedTerms
