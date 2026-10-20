/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Specialization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Specializations along flat morphisms

Flat morphisms of algebraic spaces lift generalizations whose affine étale
chart and self-pullback fibres are finite. In particular, the induced maps on
points are generalizing when the target is decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `f : Y ⟶ X` be a flat morphism of algebraic spaces over a scheme.
If `x'` specializes to `x` and the affine étale chart and self-pullback fibres
over `x'` are finite, then every point over `x` has a generalization over `x'`. -/
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
