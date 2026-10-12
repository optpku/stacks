/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Specializations lift along étale morphisms from schemes on decent spaces

If `X` is a decent algebraic space and `x' ⤳ x` in `|X|`, then every étale
morphism from a scheme lifts that specialization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.12.2: Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. Let `x, x' : Points X` and assume `x' ⤳ x`, i.e., `x` is a specialization of
`x'`. Then for every étale morphism `φ : ofOver U ⟶ X` from a scheme `U` and any
`u : U.left` with `Points.mapOfOver φ u = x`, there exists a point `u' : U.left`
with `u' ⤳ u` and `Points.mapOfOver φ u' = x'`. -/
@[stacks 03IL]
theorem exists_specializes_of_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x x' : Points X} (hspec : Specializes x' x) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = x) :
    ∃ u' : U.left, Specializes u' u ∧ Points.mapOfOver φ u' = x' :=
  sorry

/-- If `X` is decent, then the map on points induced by an étale morphism from a
scheme is a generalizing map. -/
theorem generalizingMap_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    GeneralizingMap (Points.mapOfOver φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
