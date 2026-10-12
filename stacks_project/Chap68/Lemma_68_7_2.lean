/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# No specializations in étale fibres over a locally Noetherian algebraic space

An étale morphism from a scheme to a locally Noetherian algebraic space has no
nontrivial specializations among scheme points that map to the same point of the
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.7.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`φ : ofOver U ⟶ X` be an étale morphism from a scheme to `X`. Assume `u, u' : U.left`
map to the same point `x` of `Points X`, and `u' ⤳ u`. If `X` is locally Noetherian,
then `u = u'`. -/
@[stacks 0H1Q]
theorem eq_of_specializes_of_mapOfOver_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {u u' : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) (hspec : Specializes u' u) : u = u' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
