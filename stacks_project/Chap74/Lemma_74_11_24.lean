/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_24_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.24 (1): the property `P(f)` given by “`f` is locally quasi-finite”
is fpqc local on the base. -/
@[stacks 0427] #check
  (AlgebraicSpace.FiniteType.locallyQuasiFinite_isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.LocallyOfFiniteType S ⊓ @AlgebraicSpace.LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))

/- Lemma 74.11.24 (2): the property `P(f)` given by “`f` is quasi-finite” is
fpqc local on the base. -/
@[stacks 0427] #check
  (AlgebraicSpace.QuasiFinite.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.QuasiFinite S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
