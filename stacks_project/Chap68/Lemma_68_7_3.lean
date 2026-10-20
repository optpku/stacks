module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Specialization
import StacksCheckRecall

/-!
# Specializations lift along étale morphisms from schemes

If `x' ⤳ x` on the points of an algebraic space and the pair `(X, x')`
satisfies the equivalent finite-above conditions of Lemma 68.4.5, then
every étale morphism from a scheme lifts that specialization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.7.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x, x' : Points X` and assume `x' ⤳ x`, i.e., `x` is a specialization of `x'`.
Assume the pair `(X, x')` satisfies `forallAffineEtaleFiniteAbove X x'`. Then for
every étale morphism `φ : ofOver U ⟶ X` from a scheme `U` and any `u : U.left`
with `Points.mapOfOver φ u = x`, there exists a point `u' : U.left` with
`u' ⤳ u` and `Points.mapOfOver φ u' = x'`. -/
@[stacks 03K2]
#check (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_forallAffineEtaleFiniteAbove :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {x x' : Points X} (hspec : Specializes x' x)
    (h_finiteAbove : forallAffineEtaleFiniteAbove X x') {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = x),
    ∃ u' : U.left, Specializes u' u ∧ Points.mapOfOver φ u' = x')

/- The lifting of specializations along étale morphisms from schemes also holds
under the equivalent étale covering finite-above test
`existsEtaleCoverFiniteAbove X x'`. -/
#check (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_existsEtaleCoverFiniteAbove :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {x x' : Points X} (hspec : Specializes x' x)
    (h_cover : existsEtaleCoverFiniteAbove X x') {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = x),
    ∃ u' : U.left, Specializes u' u ∧ Points.mapOfOver φ u' = x')

end AlgebraicGeometry.AlgebraicSpace
