/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap68.Lemma_68_4_5_Fibre
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Specializations lift along flat morphisms of algebraic spaces

If `x' ⤳ x` on the points of an algebraic space and the pair `(X, x')`
satisfies the equivalent finite-above conditions of Lemma 68.4.5, then
every flat morphism of algebraic spaces lifts that specialization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.7.4: Let `S` be a scheme. Let `f : Y ⟶ X` be a flat morphism of
algebraic spaces over `S`. Let `x, x' : Points X` and assume `x' ⤳ x`, i.e.,
`x` is a specialization of `x'`. Assume the pair `(X, x')` satisfies
`forallAffineEtaleFiniteAbove X x'`. Then for every `y : Points Y` with
`Points.map f y = x`, there exists a point `y' : Points Y` with `y' ⤳ y` and
`Points.map f y' = x'`. -/
@[stacks 0B7W]
theorem exists_specializes_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Flat f] {x x' : Points X} (hspec : Specializes x' x)
    (h_finiteAbove : forallAffineEtaleFiniteAbove X x') {y : Points Y}
    (hy : Points.map f y = x) :
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x' :=
  sorry

/-- The lifting of specializations along a flat morphism of algebraic spaces also
holds under the equivalent étale covering finite-above test
`existsEtaleCoverFiniteAbove X x'`. -/
theorem exists_specializes_of_flat_of_existsEtaleCoverFiniteAbove
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f]
    {x x' : Points X} (hspec : Specializes x' x)
    (h_cover : existsEtaleCoverFiniteAbove X x') {y : Points Y}
    (hy : Points.map f y = x) :
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x' :=
  sorry

/-- If `X` is decent, then the map on points induced by a flat morphism of
algebraic spaces is a generalizing map. -/
theorem generalizingMap_map_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Flat f] [IsDecent X] : GeneralizingMap (Points.map f) :=
  sorry

/-- If `X` is decent, then specializations lift along a flat morphism of
algebraic spaces. -/
theorem exists_specializes_of_flat_of_isDecent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f] [IsDecent X]
    {x x' : Points X} (hspec : Specializes x' x) {y : Points Y}
    (hy : Points.map f y = x) :
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x' :=
  sorry

/-- If `X` is quasi-separated, then specializations lift along a flat morphism of
algebraic spaces. -/
theorem exists_specializes_of_flat_of_isQuasiSeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f] [IsQuasiSeparated X]
    {x x' : Points X} (hspec : Specializes x' x) {y : Points Y}
    (hy : Points.map f y = x) :
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x' :=
  sorry

/-- If `X` is representable by a scheme, then specializations lift along a flat
morphism of algebraic spaces. -/
theorem exists_specializes_of_flat_of_isScheme {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f] [IsScheme X]
    {x x' : Points X} (hspec : Specializes x' x) {y : Points Y}
    (hy : Points.map f y = x) :
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
