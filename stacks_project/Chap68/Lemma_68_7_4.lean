module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat.Specialization
import StacksCheckRecall

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

/- Lemma 68.7.4: Let `S` be a scheme. Let `f : Y ⟶ X` be a flat morphism of
algebraic spaces over `S`. Let `x, x' : Points X` and assume `x' ⤳ x`, i.e.,
`x` is a specialization of `x'`. Assume the pair `(X, x')` satisfies
`forallAffineEtaleFiniteAbove X x'`. Then for every `y : Points Y` with
`Points.map f y = x`, there exists a point `y' : Points Y` with `y' ⤳ y` and
`Points.map f y' = x'`. -/
@[stacks 0B7W] #check (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Flat f] {x x' : Points X} (hspec : Specializes x' x)
    (h_finiteAbove : forallAffineEtaleFiniteAbove X x') {y : Points Y}
    (hy : Points.map f y = x),
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x')

#check (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_flat_of_existsEtaleCoverFiniteAbove :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f]
    {x x' : Points X} (hspec : Specializes x' x)
    (h_cover : existsEtaleCoverFiniteAbove X x') {y : Points Y}
    (hy : Points.map f y = x),
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x')

#check (AlgebraicGeometry.AlgebraicSpace.generalizingMap_map_of_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Flat f] [IsDecent X],
    GeneralizingMap (Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_flat_of_isDecent :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f] [IsDecent X]
    {x x' : Points X} (hspec : Specializes x' x) {y : Points Y}
    (hy : Points.map f y = x),
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x')

#check (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_flat_of_isQuasiSeparated :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f] [IsQuasiSeparated X]
    {x x' : Points X} (hspec : Specializes x' x) {y : Points Y}
    (hy : Points.map f y = x),
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x')

#check (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_flat_of_isScheme :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Flat f] [IsScheme X]
    {x x' : Points X} (hspec : Specializes x' x) {y : Points Y}
    (hy : Points.map f y = x),
    ∃ y' : Points Y, Specializes y' y ∧ Points.map f y' = x')

end AlgebraicGeometry.AlgebraicSpace
