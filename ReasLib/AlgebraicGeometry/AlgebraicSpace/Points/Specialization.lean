/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import Mathlib.Topology.Inseparable

/-!
# Specializations along étale morphisms

For an étale morphism from a scheme to an algebraic space, a generalization of
the image of a point lifts to a generalization of that point when the affine
étale chart and self-pullback fibres over the generalization are finite.
In particular, generalizations lift when the algebraic space is decent.
Two scheme points in the same fibre over a decent algebraic space related by
specialization are equal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A specialization whose general point has finite affine étale chart and
self-pullback fibres lifts along every étale morphism from a scheme at every
point over its special point. -/
@[stacks 03K2]
theorem exists_specializes_of_forallAffineEtaleFiniteAbove {S : Scheme.{u}}
    {X : AlgebraicSpace S} {x x' : Points X} (hspec : Specializes x' x)
    (h_finiteAbove : forallAffineEtaleFiniteAbove X x') {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = x) :
    ∃ u' : U.left, Specializes u' u ∧ Points.mapOfOver φ u' = x' :=
  sorry

/-- A specialization whose general point admits an étale scheme covering with
finite chart and self-pullback fibres lifts along every étale morphism from a
scheme at every point over its special point. -/
theorem exists_specializes_of_existsEtaleCoverFiniteAbove {S : Scheme.{u}}
    {X : AlgebraicSpace S} {x x' : Points X} (hspec : Specializes x' x)
    (h_cover : existsEtaleCoverFiniteAbove X x') {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = x) :
    ∃ u' : U.left, Specializes u' u ∧ Points.mapOfOver φ u' = x' := by
  exact exists_specializes_of_forallAffineEtaleFiniteAbove hspec
    ((forallAffineEtaleFiniteAbove_iff_existsEtaleCoverFiniteAbove X x').mpr h_cover) φ hu

/-- Two points of a scheme with the same image under an étale morphism to a
decent algebraic space are equal if one specializes to the other. -/
@[stacks 03K5]
theorem eq_of_specializes_of_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {u u' : U.left} (hmap : Points.mapOfOver φ u = Points.mapOfOver φ u')
    (hspec : Specializes u' u) : u = u' :=
  sorry

/-- Every generalization of the image of a scheme point in a decent algebraic
space lifts to a generalization of that point along an étale morphism. -/
theorem exists_specializes_of_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x x' : Points X} (hspec : Specializes x' x) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = x) :
    ∃ u' : U.left, Specializes u' u ∧ Points.mapOfOver φ u' = x' :=
  sorry

/-- The map on points induced by an étale morphism from a scheme to a decent
algebraic space is generalizing. -/
theorem generalizingMap_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    GeneralizingMap (Points.mapOfOver φ) := by
  intro u x' hspec
  exact exists_specializes_of_isDecent (X := X) (x := Points.mapOfOver φ u)
    (x' := x') hspec φ rfl

end AlgebraicGeometry.AlgebraicSpace
