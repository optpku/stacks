/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Over
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.11.3 -- Local characterization of relative gerbes

The generic local properties belong to morphisms of fibred categories. The source statement is
their factorization-invariant characterization for stack morphisms, exposed by
`StackOver.Groupoids.Hom.IsGerbeMorphism.iff_factorization`.
-/

namespace CategoryTheory

/- Lemma 8.11.3: an arbitrary groupoid-fibred factorization of a stack morphism is a gerbe for
the inherited topology exactly when the original morphism satisfies the two local conditions. -/
#check @CartesianBasedFunctor.LocallyEssentiallySurjective
#check @CartesianBasedFunctor.LocallyLifts
@[stacks 06P1 "factorization criterion for a gerbe over a stack"]
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.iff_factorization
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.iff_factorization_of_eq
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.iff_exists_factorization

end CategoryTheory
