/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_3_Etale
public import stacks_project.Chap66.Lemma_66_18_3_Site

/-!
# Comparison of the small étale site with the étale site of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.18.3 (1): the functor `smallEtaleSite X ⥤ spacesEtaleSite X` sending `U / X` to
`U / X` is special cocontinuous. -/
@[stacks 03G1]
instance smallEtaleInclusion_isSpecialCocontinuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).IsSpecialCocontinuous (smallEtaleTopology X)
      (spacesEtaleTopology X) :=
  sorry

/-- Lemma 66.18.3 (2): the cocontinuous direct image along `smallEtaleInclusion X` is an
equivalence `Sheaf (smallEtaleTopology X) ⥤ Sheaf (spacesEtaleTopology X)` on sheaves of types. -/
@[stacks 03G1]
instance smallEtaleInclusion_directImage_isEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ((smallEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (smallEtaleTopology X) (spacesEtaleTopology X)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
