/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_4_2_Fibre

/-!
# No specializations in étale fibres with finite étale covering

An étale morphism from a scheme to an algebraic space has no nontrivial
specializations among scheme points that map to the same point, whenever that
point satisfies the equivalent finite-fibre conditions of Lemma 68.4.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.7.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`φ : ofOver U ⟶ X` be an étale morphism from a scheme to `X`. Assume `u, u' : U.left`
map to the same point `x` of `Points X`, and `u' ⤳ u`. If the pair `(X, x)`
satisfies `existsEtaleCoverFiniteFibre X x`, then `u = u'`. -/
@[stacks 03IM]
theorem eq_of_specializes_of_existsEtaleCoverFiniteFibre {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {u u' : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) (hspec : Specializes u' u)
    (h_finiteFibre : existsEtaleCoverFiniteFibre X x) : u = u' :=
  sorry

/-- The uniqueness of Lemma 68.7.1 also holds under the equivalent affine étale
finite-fibre test `forallAffineEtaleFiniteFibre X x`. -/
theorem eq_of_specializes_of_forallAffineEtaleFiniteFibre {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {u u' : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) (hspec : Specializes u' u)
    (h_affine : forallAffineEtaleFiniteFibre X x) : u = u' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
