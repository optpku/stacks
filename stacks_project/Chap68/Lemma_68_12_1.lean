module

public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# No specializations in étale fibres over a decent algebraic space

An étale morphism from a scheme to a decent algebraic space has no nontrivial
specializations among scheme points that map to the same point of the algebraic
space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.12.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `φ : ofOver U ⟶ X` be an étale morphism from a scheme to `X`. If `u, u' : U.left`
map to the same point of `Points X`, and `u' ⤳ u`, then `u = u'`. -/
@[stacks 03K5]
theorem eq_of_specializes_of_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {u u' : U.left} (hmap : Points.mapOfOver φ u = Points.mapOfOver φ u')
    (hspec : Specializes u' u) : u = u' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
