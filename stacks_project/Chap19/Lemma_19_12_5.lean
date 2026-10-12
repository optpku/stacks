/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FunctorialApproximation.TermwiseInjective
import StacksCheckRecall

@[expose] public section

/-!
# Functorial Complex Approximations with Injective Factors

The reusable data and existence theorem for Lemma 19.12.5 are owned by
`FunctorialComplexApproximation.WithInjectiveFactors`. This source file is only the tagged,
source-facing check of that API.
-/

open CategoryTheory

universe w v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/- Lemma 19.12.5: a Grothendieck abelian category admits a functorial termwise-monomorphic
quasi-isomorphic enlargement whose degreewise comparison maps factor through injective
subobjects. -/
@[stacks 079N] #check
  (FunctorialComplexApproximation.WithInjectiveFactors.nonempty (C := C) :
    Nonempty (FunctorialComplexApproximation.WithInjectiveFactors C))

/- The source-facing existential view is also reusable without importing this chapter. -/
#check @FunctorialComplexApproximation.WithInjectiveFactors.exists_approximation

end CochainComplex
