/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Topology.Bases
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ForgetToTop
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Points
public import ReasLib.Topology.Category.TopCat.Limits.Recognition

/-!
# Directed affine inverse limits as topological spaces

A directed inverse limit of decent algebraic spaces with affine transitions
remains a limit after applying the underlying-topological-space functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit PreservesLimit)
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

/-- Projection-preimages of opens in the stages form a basis for the canonical
topology on the points of a limiting cone. -/
theorem isTopologicalBasis_preimage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    IsTopologicalBasis
      (setOf fun (U : Set (Points c.pt)) ↦
        ∃ (i : OrderDual I) (V : Set (Points (D.obj i))),
          IsOpen V ∧ U = (Points.map (c.π.app i)) ⁻¹' V) :=
  sorry

-- These implementation definitions must remain private while supplying the
-- concrete data in the public limiting-cone construction.
set_option backward.privateInPublic true in
/-- Inverting the canonical comparison sends a compatible family arising from
a cone of point sets to a point of the limiting algebraic space. -/
private def pointsLimitLift
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (s : Cone (D ⋙ pointsFunctor)) (x : s.pt) : Points c.pt :=
  (Equiv.ofBijective (CategoryTheory.Limits.Types.sectionOfCone (pointsFunctor.mapCone c))
    (bijective_sectionOfCone D c hc)).symm (CategoryTheory.Limits.Types.sectionOfCone s x)

/-- The inverse-comparison lift commutes with every projection of the cone. -/
private theorem pointsLimitLift_fac
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (s : Cone (D ⋙ pointsFunctor))
    (j : OrderDual I) (x : s.pt) :
    Points.map (c.π.app j) (pointsLimitLift D c hc s x) = s.π.app j x :=
  sorry

/-- A map compatible with every cone projection equals the inverse-comparison lift. -/
private theorem pointsLimitLift_uniq
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (s : Cone (D ⋙ pointsFunctor))
    (m : s.pt → Points c.pt)
    (hm : ∀ (j : OrderDual I) (x : s.pt),
      Points.map (c.π.app j) (m x) = s.π.app j x)
    (x : s.pt) :
    m x = pointsLimitLift D c hc s x :=
  sorry

set_option backward.privateInPublic true in
/-- The inverse of the canonical point comparison supplies the limiting cone
of point sets. -/
private def pointsIsLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    IsLimit (pointsFunctor.mapCone c) where
  lift s := TypeCat.ofHom (pointsLimitLift D c hc s)
  fac s j := by
    ext x
    exact pointsLimitLift_fac D c hc s j x
  uniq s m hm := by
    ext x
    exact pointsLimitLift_uniq D c hc s m
      (fun j x ↦ CategoryTheory.ConcreteCategory.congr_hom (hm j) x) x

-- The explicit construction uses private limiting-cone data. This declaration-scoped
-- option permits that reference while keeping the implementation helpers private.
set_option backward.privateInPublic true in
/-- A limiting cone of a directed affine system of decent algebraic spaces
remains limiting on underlying topological spaces. -/
def isLimit_forgetToTop_mapCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    IsLimit (forgetToTop.mapCone c) :=
  TopCat.Cone.isLimit_of_forgetIsLimit_of_preimageBasis.{u + 1, u, u}
    (forgetToTop.mapCone c)
    (by
      change IsLimit (pointsFunctor.mapCone c)
      exact pointsIsLimit D c hc)
    (isTopologicalBasis_preimage D c hc)

/-- The underlying-topological-space functor preserves limits of directed
inverse diagrams of decent algebraic spaces whose transition morphisms are affine. -/
instance preservesLimit_forgetToTop
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)] :
    PreservesLimit D forgetToTop where
  preserves hc := ⟨isLimit_forgetToTop_mapCone D _ hc⟩

/-- The chosen directed affine inverse limit of decent algebraic spaces has
underlying space equal to the inverse limit of the stagewise spaces. -/
def isLimit_forgetToTop_mapCone_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)] :
    IsLimit (forgetToTop.mapCone (Limits.limit.cone D)) :=
  isLimit_forgetToTop_mapCone D (Limits.limit.cone D) (Limits.limit.isLimit D)

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
