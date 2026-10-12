/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# The reduction inclusion as a universal homeomorphism of algebraic spaces

The canonical closed immersion from the reduction of an algebraic space is a
universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.53.6: The canonical closed immersion from the reduction of an algebraic
space is a universal homeomorphism. -/
@[stacks 08AK]
instance instUniversalHomeomorphism_reductionι {S : Scheme.{u}} {X : AlgebraicSpace S} :
    UniversalHomeomorphism (reductionι X) := sorry

end AlgebraicGeometry.AlgebraicSpace
