/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Limit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Points of directed affine inverse limits of algebraic spaces

The points of a directed inverse limit of decent algebraic spaces with affine
transitions are the compatible families of stagewise points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit)
open CategoryTheory.Limits.Types (sectionOfCone)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

/-- The canonical comparison `sectionOfCone` of a points cone is stagewise
`Points.map` of the cone projections. -/
theorem sectionOfCone_apply {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    (i : OrderDual I) :
    (sectionOfCone (pointsFunctor.mapCone c) x).val i =
      Points.map (c.π.app i) x :=
  sorry

/-- For a limiting cone of a directed inverse system of decent algebraic spaces
over `S` with affine transition morphisms, the canonical map from the points of
the limit to compatible families of stagewise points is bijective. -/
theorem bijective_sectionOfCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    Function.Bijective (sectionOfCone (pointsFunctor.mapCone c)) :=
  sorry

/-- A limiting cone of a directed affine system of decent algebraic spaces
remains limiting on points, up to existence of an `IsLimit` structure. -/
theorem isLimit_pointsFunctor_mapCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    Nonempty (IsLimit (pointsFunctor.mapCone c)) :=
  sorry

/-- The chosen directed affine inverse limit of decent algebraic spaces has
points equal to the inverse limit of the stagewise points, as sets. -/
theorem bijective_sectionOfCone_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)] :
    Function.Bijective
      (sectionOfCone (pointsFunctor.mapCone (Limits.limit.cone D))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
