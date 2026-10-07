module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Topology.Bases
public import stacks_project.Chap70.Lemma_70_5_2_ForgetToTop

/-!
# Directed affine inverse limits as topological spaces

A directed inverse limit of decent algebraic spaces with affine transitions
remains a limit after applying `forgetToTop`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit PreservesLimit isLimitOfPreserves)
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

/-- The underlying-topological-space functor preserves limits of directed
inverse diagrams of decent algebraic spaces whose transition morphisms are
affine. -/
instance preservesLimit_forgetToTop
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)] :
    PreservesLimit D forgetToTop :=
  sorry

/-- A limiting cone of a directed affine system of decent algebraic spaces
remains limiting on underlying topological spaces. -/
noncomputable def isLimit_forgetToTop_mapCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    IsLimit (forgetToTop.mapCone c) :=
  isLimitOfPreserves forgetToTop hc

/-- The chosen directed affine inverse limit of decent algebraic spaces has
underlying space equal to the inverse limit of the stagewise spaces. -/
noncomputable def isLimit_forgetToTop_mapCone_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)] :
    IsLimit (forgetToTop.mapCone (Limits.limit.cone D)) :=
  isLimit_forgetToTop_mapCone D (Limits.limit.cone D) (Limits.limit.isLimit D)

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
